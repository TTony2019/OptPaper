#!/usr/bin/env python3
"""Translate the last Lean declaration in each missing NL Markdown file.

Configuration is loaded from Claude Code's ``~/.claude/settings.json`` by
default. Explicit process environment variables and command-line options take
precedence over values from that file.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from string import Template
import tempfile
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path


DECLARATION_KEYWORDS = {
    "theorem",
    "lemma",
    "corollary",
    "proposition",
    "def",
    "abbrev",
    "opaque",
    "structure",
    "class",
    "inductive",
    "coinductive",
    "instance",
    "axiom",
    "constant",
    "example",
    "recall",
}
MODIFIERS = {
    "private",
    "protected",
    "noncomputable",
    "unsafe",
    "partial",
    "scoped",
}
PROOF_DECLARATIONS = {"theorem", "lemma", "corollary", "proposition", "example"}


def load_claude_settings(path: Path) -> None:
    """Load environment variables from Claude Code's settings JSON.

    Only the top-level ``env`` object is relevant to this script. Existing
    process environment variables are kept, so explicit shell overrides win.
    Invalid or absent settings files are ignored so the script still works
    with explicit command-line options and environment variables.
    """
    if not path.is_file():
        return
    try:
        settings = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return
    if not isinstance(settings, dict) or not isinstance(settings.get("env"), dict):
        return
    for key, value in settings["env"].items():
        if not isinstance(key, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
            continue
        if isinstance(value, (str, int, float, bool)):
            os.environ.setdefault(key, str(value))


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    source: str
    statement: str
    proof: str | None


def _mask_comments_and_strings(source: str) -> str:
    """Replace comments and strings with spaces while preserving positions."""
    chars = list(source)
    i = 0
    n = len(source)
    block_depth = 0
    while i < n:
        if block_depth:
            if source.startswith("/-", i):
                chars[i] = chars[i + 1] = " "
                block_depth += 1
                i += 2
            elif source.startswith("-/", i):
                chars[i] = chars[i + 1] = " "
                block_depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    chars[i] = " "
                i += 1
            continue
        if source.startswith("/-", i):
            chars[i] = chars[i + 1] = " "
            block_depth = 1
            i += 2
        elif source[i] == "-" and i + 1 < n and source[i + 1] == "-":
            while i < n and source[i] != "\n":
                chars[i] = " "
                i += 1
        elif source[i] == '"':
            chars[i] = " "
            i += 1
            while i < n:
                if source[i] == "\n":
                    break
                escaped = source[i] == "\\" and i + 1 < n
                chars[i] = " "
                i += 1
                if escaped:
                    chars[i] = " "
                    i += 1
                elif source[i - 1] == '"':
                    break
        else:
            i += 1
    return "".join(chars)


def _depths(masked: str) -> list[int]:
    depths = [0] * len(masked)
    depth = 0
    opening = "([{"
    closing = ")] }".replace(" ", "")
    for i, char in enumerate(masked):
        depths[i] = depth
        if char in opening:
            depth += 1
        elif char in closing and depth:
            depth -= 1
    return depths


def _declaration_starts(source: str, masked: str) -> list[tuple[int, str, str]]:
    depths = _depths(masked)
    starts: list[tuple[int, str, str]] = []
    pattern = re.compile(
        r"(?m)^[ \t]*(?P<prefix>(?:(?:" + "|".join(MODIFIERS) + r")[ \t]+)*)"
        r"(?P<kind>" + "|".join(DECLARATION_KEYWORDS) + r")[ \t]+"
        r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
    )
    for match in pattern.finditer(masked):
        if depths[match.start()] != 0:
            continue
        starts.append((match.start(), match.group("kind"), match.group("name")))
    return starts


def _trim_trailing_ends(text: str) -> str:
    lines = text.splitlines()
    while lines and (not lines[-1].strip() or re.fullmatch(r"\s*end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*", lines[-1])):
        lines.pop()
    return "\n".join(lines).strip()


def _find_top_level_assignment(masked: str) -> int | None:
    depths = _depths(masked)
    for match in re.finditer(r":=", masked):
        if depths[match.start()] == 0:
            return match.start()
    return None


def extract_last_declaration(source: str) -> Declaration | None:
    masked = _mask_comments_and_strings(source)
    starts = _declaration_starts(source, masked)
    if not starts:
        return None
    start, kind, name = starts[-1]
    end = len(source)
    text = _trim_trailing_ends(source[start:end])
    relative_assignment = _find_top_level_assignment(masked[start : start + len(text)])
    if kind not in PROOF_DECLARATIONS or relative_assignment is None:
        statement, proof = text, None
    else:
        statement = text[:relative_assignment].rstrip()
        proof = text[relative_assignment + 2 :].strip() or None
    return Declaration(kind=kind, name=name, source=text, statement=statement, proof=proof)


def output_path_for(lean_path: Path, theorem_root: Path, output_root: Path) -> Path:
    return output_root / lean_path.relative_to(theorem_root).with_suffix(".md")


PROMPT_PATH = Path(__file__).with_name("translation_prompt.txt")
PROMPT_SEPARATOR = "===PROOF_EXPLANATION==="
SYSTEM_PROMPT = (
    "You are an expert in mathematics, Lean 4, and Mathlib. "
    "Follow the supplied Lean source exactly and do not add assumptions or conclusions."
)


def build_prompt(declaration: Declaration, relative_path: str, prompt_path: Path = PROMPT_PATH) -> str:
    """Fill the external English translation prompt with one declaration."""
    proof_text = declaration.proof if declaration.proof is not None else "-- No separate proof part."
    template = Template(prompt_path.read_text(encoding="utf-8"))
    return template.substitute(
        relative_path=relative_path,
        declaration_kind=declaration.kind,
        declaration_name=declaration.name,
        statement=declaration.statement,
        proof=proof_text,
        separator=PROMPT_SEPARATOR,
    )


def split_explanations(response: str) -> tuple[str, str]:
    """Split the model response into statement and proof explanations."""
    statement, separator, proof = response.partition(PROMPT_SEPARATOR)
    if not separator:
        return response.strip(), "No proof explanation was returned by the model."
    return statement.strip(), proof.strip()


def render_markdown(declaration: Declaration, relative_path: str, response: str) -> str:
    """Render the requested English Markdown layout deterministically."""
    statement_explanation, proof_explanation = split_explanations(response)
    proof_text = declaration.proof if declaration.proof is not None else "-- No separate proof part."
    return f"""## Source file
`{relative_path}`

## Lean statement
```lean
{declaration.statement}
```

## Statement explanation
{statement_explanation}

## Lean proof
```lean
{proof_text}
```

## Proof explanation
{proof_explanation}
"""


class AnthropicClient:
    """Small dependency-free client for DeepSeek's Anthropic-compatible API."""

    def __init__(
        self,
        api_key: str,
        base_url: str,
        model: str,
        timeout: float,
        retries: int,
        max_tokens: int = 8192,
    ):
        self.api_key = api_key
        self.endpoint = base_url.rstrip("/") + "/v1/messages"
        self.model = model
        self.timeout = timeout
        self.retries = retries
        self.max_tokens = max_tokens

    def translate(self, prompt: str) -> str:
        payload = json.dumps(
            {
                "model": self.model,
                "max_tokens": self.max_tokens,
                "system": SYSTEM_PROMPT,
                "messages": [
                    {
                        "role": "user",
                        "content": [{"type": "text", "text": prompt}],
                    }
                ],
                "stream": False,
                "temperature": 0.2,
            }
        ).encode("utf-8")
        request = urllib.request.Request(
            self.endpoint,
            data=payload,
            headers={
                "x-api-key": self.api_key,
                "anthropic-version": "2023-06-01",
                "Content-Type": "application/json",
                "Accept": "application/json",
            },
            method="POST",
        )
        last_error: Exception | None = None
        for attempt in range(self.retries + 1):
            try:
                with urllib.request.urlopen(request, timeout=self.timeout) as response:
                    body = json.loads(response.read().decode("utf-8"))
                content = body["content"]
                if isinstance(content, str):
                    return content.strip()
                text_blocks = [
                    block["text"]
                    for block in content
                    if isinstance(block, dict) and block.get("type") == "text" and isinstance(block.get("text"), str)
                ]
                if not text_blocks:
                    raise KeyError("content text block")
                return "\n".join(text_blocks).strip()
            except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, KeyError, IndexError, json.JSONDecodeError) as exc:
                last_error = exc
                if attempt < self.retries:
                    time.sleep(2 ** attempt)
        raise RuntimeError(f"DeepSeek request failed after {self.retries + 1} attempts: {last_error}")


def write_atomic(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(content)
        handle.write("\n")
    os.replace(temporary, path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theorem-root", type=Path, default=Path("TheoremLib"))
    parser.add_argument("--output-root", type=Path, default=Path("NL"))
    parser.add_argument(
        "--claude-settings",
        type=Path,
        default=Path.home() / ".claude" / "settings.json",
        help="Claude Code settings JSON to load (default: ~/.claude/settings.json)",
    )
    parser.add_argument(
        "--no-claude-settings",
        action="store_true",
        help="Do not load Claude Code settings; use process environment and defaults",
    )
    parser.add_argument(
        "--base-url",
        default=None,
    )
    parser.add_argument(
        "--model",
        default=None,
    )
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--retries", type=int, default=3)
    parser.add_argument("--delay", type=float, default=0.0, help="Seconds to wait between successful requests")
    parser.add_argument("--limit", type=int, default=0, help="Process at most N missing files (0 means all)")
    parser.add_argument("--file", type=Path, help="Process one Lean file")
    parser.add_argument("--force", action="store_true", help="Translate existing Markdown files too")
    parser.add_argument("--dry-run", action="store_true", help="List missing files without calling the API")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if not args.no_claude_settings:
        load_claude_settings(args.claude_settings.expanduser())
    base_url = args.base_url or os.getenv(
        "ANTHROPIC_BASE_URL", os.getenv("DEEPSEEK_BASE_URL", "https://api.deepseek.com/anthropic")
    )
    model = args.model or os.getenv("ANTHROPIC_MODEL", os.getenv("DEEPSEEK_MODEL", "deepseek-v4-pro"))
    theorem_root = args.theorem_root.resolve()
    output_root = args.output_root.resolve()
    if not theorem_root.is_dir():
        print(f"Theorem root does not exist: {theorem_root}", file=sys.stderr)
        return 2
    if args.file:
        lean_files = [args.file.resolve()]
    else:
        lean_files = sorted(theorem_root.rglob("*.lean"))
    candidates = []
    for lean_path in lean_files:
        if not lean_path.is_file() or theorem_root not in lean_path.parents:
            continue
        output_path = output_path_for(lean_path, theorem_root, output_root)
        if not args.force and output_path.exists():
            continue
        candidates.append((lean_path, output_path))
    if args.limit > 0:
        candidates = candidates[: args.limit]
    print(f"Found {len(candidates)} file(s) to process.")
    if args.dry_run:
        for lean_path, output_path in candidates:
            print(f"{lean_path.relative_to(theorem_root)} -> {output_path.relative_to(output_root)}")
        return 0
    api_key = os.getenv(
        "ANTHROPIC_AUTH_TOKEN",
        os.getenv("ANTHROPIC_API_KEY", os.getenv("DEEPSEEK_API_KEY", "")),
    ).strip()
    if not api_key:
        print(
            "No API key found; set ANTHROPIC_AUTH_TOKEN in Claude settings, "
            "the environment, or pass it through the settings file before "
            "running without --dry-run.",
            file=sys.stderr,
        )
        return 2
    client = AnthropicClient(api_key, base_url, model, args.timeout, args.retries, args.max_tokens)
    failures = 0
    for index, (lean_path, output_path) in enumerate(candidates, 1):
        relative_path = str(lean_path.relative_to(theorem_root))
        try:
            declaration = extract_last_declaration(lean_path.read_text(encoding="utf-8"))
            if declaration is None:
                content = (
                    f"## Source file\n`{relative_path}`\n\n"
                    "## Lean statement\n"
                    "No recognizable Lean declaration was found.\n\n"
                    "## Statement explanation\n"
                    "There is no statement to explain.\n\n"
                    "## Lean proof\n```lean\n-- No separate proof part.\n```\n\n"
                    "## Proof explanation\nThere is no proof to explain."
                )
                write_atomic(output_path, content)
            else:
                response = client.translate(build_prompt(declaration, relative_path))
                write_atomic(output_path, render_markdown(declaration, relative_path, response))
            print(f"[{index}/{len(candidates)}] wrote {output_path.relative_to(output_root)}")
        except Exception as exc:  # keep the batch moving when one file fails
            failures += 1
            print(f"[{index}/{len(candidates)}] FAILED {relative_path}: {exc}", file=sys.stderr)
        if args.delay and index < len(candidates):
            time.sleep(args.delay)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
