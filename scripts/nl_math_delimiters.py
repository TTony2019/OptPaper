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
# GitHub's MathJax build refuses these, reporting "The following macros are not
# allowed: <name>", so they are rewritten to the equivalent it does accept.
BLOCKED_MACROS = [
    (re.compile(r"\\operatorname\*?\{(?:[^{}]|\{[^{}]*\})*\}"),
     lambda match: r"\mathrm{" + match.group(0)[match.group(0).index("{") + 1:-1] + "}"),
    (re.compile(r"\\operatorname\*?"), r"\\mathrm"),
]


# A line consisting only of Markdown punctuation is a setext heading underline
# (``-``, ``=``) or an empty list item; either one splits the display block into
# a heading/list plus a paragraph, and GitHub then leaves the math unrendered.
LONE_MARKER = re.compile(r"^\s*[-=*+#]+\s*$")
# A list marker followed by a space turns the rest of the block into list items.
LIST_MARKER_SPACE = re.compile(r"^(\s*[-+*])\s+(?=\S)")
# A line starting with ``>`` opens a block quote, but in these formulas it is
# just a relation carrying over from the previous line.
BLOCK_QUOTE_START = re.compile(r"^\s*>")


def _reflow_display_block(body: list[str]) -> list[str]:
    """Return ``body`` reshaped so that it stays a single Markdown paragraph."""
    reflowed: list[str] = []
    index = 0
    while index < len(body):
        line = body[index]
        if BLOCK_QUOTE_START.match(line):
            if reflowed:
                reflowed[-1] = f"{reflowed[-1].rstrip()} {line.strip()}"
            elif index + 1 < len(body):
                reflowed.append(f"{line.strip()}{body[index + 1].strip()}")
                index += 1
            else:
                reflowed.append(line.strip().lstrip("> "))
            index += 1
            continue
        if LONE_MARKER.match(line):
            marker = line.strip()
            if index + 1 < len(body):
                following = body[index + 1]
                indent = following[: len(following) - len(following.lstrip())]
                reflowed.append(f"{indent}{marker}{following.strip()}")
                index += 2
                continue
            if reflowed:
                reflowed[-1] = reflowed[-1].rstrip() + " " + marker
                index += 1
                continue
        reflowed.append(LIST_MARKER_SPACE.sub(r"\1", line))
        index += 1
    return reflowed


def _rewrite_blocked_macros(tex: str) -> str:
    for pattern, replacement in BLOCKED_MACROS:
        tex = pattern.sub(replacement, tex)
    return tex


# GitHub's Markdown layer strips the backslash from every ``\`` + punctuation
# pair inside math, so ``\|x\|`` reaches MathJax as ``|x|``, ``\,`` as a comma
# and ``\{`` as a plain brace. Formulas containing such a pair are therefore
# written with GitHub's backtick delimiters, where the text is passed through
# verbatim.
ESCAPED_PUNCTUATION = re.compile(r"\\+[!-/:-@\[-`{-~]")
# A doubled backslash is a line break in LaTeX and loses one backslash too.
DOUBLED_BACKSLASH = re.compile(r"\\\\")
PLAIN_INLINE_SPAN = re.compile(r"(?<!\$)\$(?!`)([^$\n`]+)\$(?!\$)")
PROTECTED_INLINE_SPAN = re.compile(r"(?<!\$)\$`([^`\n]+)`\$")
FENCE_BODY = re.compile(r"^```")


def _needs_protection(tex: str) -> bool:
    """True when Markdown would eat part of ``tex`` before MathJax sees it."""
    if "`" in tex:
        return False
    return bool(ESCAPED_PUNCTUATION.search(tex) or DOUBLED_BACKSLASH.search(tex))


def _inline_span(content: str) -> str:
    """Delimit one inline formula the way GitHub needs it."""
    # Markdown reads a bare ``<`` as the start of an HTML tag and then leaves
    # the whole inline formula unrendered, so the relation is spelled with the
    # LaTeX aliases. The trailing space only ends the command name; math mode
    # drops it and text mode swallows it.
    content = content.replace("<", r"\lt ").replace(">", r"\gt ").strip()
    if _needs_protection(content):
        return "$`" + content + "`$"
    return "$" + content + "$"


def _protect_existing_spans(line: str) -> str:
    """Move escapers already wrapped in ``$...$`` into the protected form."""
    return PLAIN_INLINE_SPAN.sub(
        lambda match: _inline_span(_rewrite_blocked_macros(match.group(1))), line
    )


def _convert_inline(line: str, *, pad: bool, protect: bool = True) -> str:
    """Convert ``\\(...\\)`` spans on one line into the GitHub delimiters.

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
        result += _inline_span(_rewrite_blocked_macros(match.group(1).strip()))
        # A closing ``$`` followed by a letter or digit is not recognised
        # either, so keep a space in that case as well.
        if pad and end < len(line) and line[end].isalnum():
            result += " "
        last = end
    result += line[last:]
    if not protect:
        # Inside a display block the ``$`` characters belong to the formula.
        return result
    # Whatever the spans looked like before, only their content may be edited.
    result = _protect_existing_spans(result)
    return PROTECTED_INLINE_SPAN.sub(
        lambda match: "$`" + _rewrite_blocked_macros(match.group(1)) + "`$", result
    )


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
        if line.strip() in (DISPLAY_OPEN, "$$"):
            closing = "$$" if line.strip() == "$$" else DISPLAY_CLOSE
            indent = line[: len(line) - len(line.lstrip())]
            index += 1
            body: list[str] = []
            while index < len(lines) and lines[index].strip() != closing:
                # Nested \(\), as emitted by ``\text{\(x\) ...}``, become the
                # ``$`` switch MathJax understands inside text mode.
                body.append(_convert_inline(lines[index], pad=False, protect=False))
                index += 1
            index += 1  # drop the closing delimiter, re-emitted below
            # A block indented under a list item is not recognised whenever the
            # list also holds inline math, so every block sits at the margin.
            body = [
                entry[len(indent):].rstrip() if entry.startswith(indent) else entry.strip()
                for entry in body
            ]
            body = _reflow_display_block(body)
            # A formula holding a backslash-escaped punctuation character goes
            # into a math fence, where Markdown passes it through untouched.
            protected = any(_needs_protection(entry) for entry in body) and not any(
                FENCE_BODY.match(entry) for entry in body
            )
            if output and output[-1].strip():
                output.append("")
            if protected:
                output.append("```math")
                output.extend(body)
                output.append("```")
            else:
                output.append("$$")
                output.extend(body)
                output.append("$$")
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
