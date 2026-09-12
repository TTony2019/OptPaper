#!/usr/bin/env python3
"""Rewrite natural-language Markdown math to the delimiters GitHub renders.

GitHub's Markdown math only recognises ``$...$`` (inline) and ``$$...$$``
(display). The ``\\(...\\)`` and ``\\[...\\]`` forms used earlier are consumed as
CommonMark backslash escapes, so the formulas reached the page as plain text.

This module converts an existing explanation, and is also applied by
``translate_last_declaration.py`` to every response the model returns, so new
translations are emitted in the GitHub dialect from the start.

Two GitHub-specific rules are enforced, both verified against the rendering
API:

* the opening ``$`` must be preceded by whitespace, otherwise the span is left
  as literal text;
* a displayed ``$$`` block must be separated from the surrounding paragraph by
  blank lines, otherwise it is not treated as a block at all.

Run ``python3 scripts/nl_math_delimiters.py --check`` to report the files that
still need rewriting, or ``--write`` to convert them in place.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re


FENCE_PREFIX = "```"
DISPLAY_OPEN = "\\["
DISPLAY_CLOSE = "\\]"
INLINE_MATH = re.compile(r"(?<!\\)\\\((.*?)\\\)")
# A hyphen sandwiched between two inline formulas, as in ``\(a\)-\(b\)``: the
# hyphen glues the two spans together, so they are merged into a single formula.
GLUED_HYPHEN = re.compile(r"\\\)\s*-\s*\\\(")


def _convert_inline(line: str, *, pad: bool) -> str:
    """Convert ``\\(...\\)`` spans on one line into ``$...$`` spans.

    ``pad`` inserts a space before a span that follows a non-space character,
    which the GitHub renderer requires outside math blocks.
    """
    line = GLUED_HYPHEN.sub(r"\\text{-}", line)
    result = ""
    last = 0
    for match in INLINE_MATH.finditer(line):
        start, end = match.span()
        result += line[last:start]
        if pad and result and not result[-1].isspace():
            result += " "
        result += "$" + match.group(1).strip() + "$"
        # A closing ``$`` followed by a letter or digit is not recognised
        # either, so keep a space in that case as well.
        if pad and end < len(line) and line[end].isalnum():
            result += " "
        last = end
    result += line[last:]
    return result


def normalize_math_delimiters(text: str) -> str:
    """Return ``text`` with every math span in the ``$``/``$$`` dialect."""
    lines = text.split("\n")
    output: list[str] = []
    in_fence = False
    index = 0
    while index < len(lines):
        line = lines[index]
        if line.lstrip().startswith(FENCE_PREFIX):
            in_fence = not in_fence
            output.append(line)
            index += 1
            continue
        if in_fence:
            output.append(line)
            index += 1
            continue
        if line.strip() == DISPLAY_OPEN:
            indent = line[: len(line) - len(line.lstrip())]
            if output and output[-1].strip():
                output.append("")
            output.append(f"{indent}$$")
            index += 1
            while index < len(lines) and lines[index].strip() != DISPLAY_CLOSE:
                # Nested \(\), as emitted by ``\text{\(x\) ...}``, become the
                # ``$`` switch that KaTeX understands inside text mode.
                output.append(_convert_inline(lines[index], pad=False))
                index += 1
            output.append(f"{indent}$$")
            index += 1  # drop the ``\]`` line, replaced by the closing ``$$``
            if index < len(lines) and lines[index].strip():
                output.append("")
            continue
        output.append(_convert_inline(line, pad=True))
        index += 1
    return "\n".join(output)


def needs_conversion(text: str) -> bool:
    """True when ``text`` still contains a non-GitHub math delimiter."""
    return bool(INLINE_MATH.search(text)) or DISPLAY_OPEN in text


def convert_tree(output_root: Path, *, write: bool) -> int:
    """Convert every Markdown file below ``output_root``; return the count."""
    changed = 0
    for path in sorted(output_root.rglob("*.md")):
        original = path.read_text(encoding="utf-8")
        converted = normalize_math_delimiters(original)
        if converted == original:
            continue
        changed += 1
        print(f"{'rewritten' if write else 'needs conversion'}: {path}")
        if write:
            temporary = path.with_suffix(path.suffix + ".tmp")
            temporary.write_text(converted, encoding="utf-8")
            temporary.replace(path)
    return changed


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-root", type=Path, default=Path("NL"))
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true", help="Report files that are not converted yet")
    group.add_argument("--write", action="store_true", help="Rewrite the files in place")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    changed = convert_tree(args.output_root, write=args.write)
    print(f"{changed} file(s) {'rewritten' if args.write else 'need conversion'} under {args.output_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
