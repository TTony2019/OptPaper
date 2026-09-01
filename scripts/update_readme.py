#!/usr/bin/env python3
"""Generate the paper formalization status section in README.md."""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import quote


ROOT = Path(__file__).resolve().parents[1]
THEOREM_LIB = ROOT / "TheoremLib"
README = ROOT / "README.md"
PAPER_METADATA = ROOT / "papers.json"

START_MARKER = "<!-- FORMALIZATION_STATUS:START -->"
END_MARKER = "<!-- FORMALIZATION_STATUS:END -->"
LOC_START_MARKER = "<!-- LOC_STATS:START -->"
LOC_END_MARKER = "<!-- LOC_STATS:END -->"
EXCLUDED_DIRECTORIES = {"Helpers", "test_paper"}

DEFINITION_FILE = re.compile(r"^(?:(?:ext_)?def|algo)_.*\.lean$")
THEOREM_FILE = re.compile(r"^(?:ext_)?(?:thm|lem|prop|cor|rem)_.*\.lean$")
OPEN_ITEM = re.compile(r"\b(?:sorry|admit|axiom|constant)\b")


@dataclass(frozen=True)
class PaperStatus:
    name: str
    display_name: str
    path: Path
    definitions: int
    proved: int
    open_items: int


@dataclass(frozen=True)
class DirectoryStats:
    files: int
    total: int
    code: int


def lean_code_without_comments_or_strings(source: str) -> str:
    """Remove nested Lean comments and quoted strings while preserving tokens."""
    result: list[str] = []
    index = 0
    block_depth = 0
    in_string = False

    while index < len(source):
        if block_depth:
            if source.startswith("/-", index):
                block_depth += 1
                index += 2
            elif source.startswith("-/", index):
                block_depth -= 1
                index += 2
            else:
                index += 1
            continue

        if in_string:
            if source[index] == "\\":
                index += 2
            elif source[index] == '"':
                in_string = False
                index += 1
            else:
                index += 1
            continue

        if source.startswith("--", index):
            newline = source.find("\n", index + 2)
            if newline == -1:
                break
            result.append("\n")
            index = newline + 1
        elif source.startswith("/-", index):
            block_depth = 1
            index += 2
        elif source[index] == '"':
            in_string = True
            index += 1
        else:
            result.append(source[index])
            index += 1

    return "".join(result)


def is_open_item(path: Path) -> bool:
    source = path.read_text(encoding="utf-8")
    return OPEN_ITEM.search(lean_code_without_comments_or_strings(source)) is not None


def count_lean_lines(directory: Path) -> DirectoryStats:
    """Count `.lean` files, total lines, and code lines in a directory tree.

    Total lines include comments and blank lines; code lines exclude them.
    """
    files = list(directory.rglob("*.lean"))
    total = 0
    code = 0
    for path in files:
        source = path.read_text(encoding="utf-8")
        total += len(source.splitlines())
        code += sum(
            1
            for line in lean_code_without_comments_or_strings(source).splitlines()
            if line.strip()
        )
    return DirectoryStats(files=len(files), total=total, code=code)


def load_paper_metadata() -> dict[str, dict[str, str | int]]:
    if not PAPER_METADATA.exists():
        return {}

    metadata = json.loads(PAPER_METADATA.read_text(encoding="utf-8"))
    if not isinstance(metadata, dict):
        raise ValueError("papers.json must contain a JSON object")
    return metadata


def clean_words(text: str) -> list[str]:
    """Split text into words, stripping LaTeX math, commands, and markup."""
    t = re.sub(r"\$[^$]*\$", " ", text)
    t = re.sub(r"\\[a-zA-Z]+", " ", t)
    t = re.sub(r"[{}*_^`]", " ", t)
    return re.findall(r"[^\W\d_]+(?:[-'][^\W\d_]+)*", t)


def first_author_surname(authors: str) -> str:
    first = authors.split(",")[0].strip()
    parts = first.split()
    return parts[-1] if parts else first


def short_display_name(name: str, metadata: dict[str, dict[str, str | int]]) -> str:
    """First-author surname + first three title words + year, joined by `_`."""
    entry = metadata.get(name)
    if entry is not None:
        try:
            authors = entry["authors"]
            title = entry["title"]
            year = entry["year"]
        except KeyError as error:
            raise ValueError(f"papers.json entry {name!r} is missing {error.args[0]!r}") from error

        if not isinstance(authors, str) or not isinstance(title, str) or not isinstance(year, int):
            raise ValueError(
                f"papers.json entry {name!r} requires string authors/title and an integer year"
            )
        parts = [first_author_surname(authors)] + clean_words(title)[:3] + [str(year)]
        return "_".join(parts)

    # No metadata: parse the directory name (Author_Title_words..._YYYY).
    base = re.sub(r"_(?:correction(?:_math)?|planclaude|plancodex|luna|sol|terra)$", "", name)
    year_match = re.search(r"_(\d{4})$", base)
    year = year_match.group(1) if year_match else ""
    if year_match:
        base = base[: year_match.start()]
    item_match = re.match(r"^item_(\d{4})_", base)
    if item_match:
        year = year or item_match.group(1)
        base = base[item_match.end():]
    parts = [p for p in base.split("_") if p]
    if not parts:
        return name
    return "_".join(parts[:1] + parts[1:4] + ([year] if year else []))


def collect_papers() -> list[PaperStatus]:
    papers: list[PaperStatus] = []
    metadata = load_paper_metadata()

    for paper_dir in sorted(THEOREM_LIB.iterdir(), key=lambda path: path.name.lower()):
        if not paper_dir.is_dir() or paper_dir.name in EXCLUDED_DIRECTORIES:
            continue

        items_dir = paper_dir / "items"
        if not items_dir.is_dir():
            continue

        definitions = 0
        proved = 0
        open_items = 0

        for item in sorted(items_dir.glob("*.lean")):
            if DEFINITION_FILE.fullmatch(item.name):
                definitions += 1
            elif THEOREM_FILE.fullmatch(item.name):
                if is_open_item(item):
                    open_items += 1
                else:
                    proved += 1

        papers.append(
            PaperStatus(
                name=paper_dir.name,
                display_name=short_display_name(paper_dir.name, metadata),
                path=paper_dir.relative_to(ROOT),
                definitions=definitions,
                proved=proved,
                open_items=open_items,
            )
        )

    return papers


def badge(label: str, value: int, color: str) -> str:
    encoded_label = quote(label.replace("-", "--"), safe="")
    return f"![{label}](https://img.shields.io/badge/{encoded_label}-{value}-{color}?style=flat-square)"


def render_status(papers: list[PaperStatus]) -> str:
    definition_total = sum(paper.definitions for paper in papers)
    proved_total = sum(paper.proved for paper in papers)
    open_total = sum(paper.open_items for paper in papers)

    lines = [
        START_MARKER,
        "",
        badge("papers", len(papers), "0f766e"),
        badge("defs_items", definition_total, "2563eb"),
        badge("proved_theorem-items", proved_total, "16a34a"),
        badge("open_theorem-items", open_total, "dc2626"),
        "",
        "Counting convention:",
        "",
        "- `definition-like items` counts `def_*`, `ext_def_*`, and `algo_*` item",
        "  files.",
        "- `theorem-like items` counts `thm_*`, `lem_*`, `prop_*`, `cor_*`, `rem_*`,",
        "  and their `ext_*` versions.",
        "- An item is marked open if its non-comment Lean code contains `sorry`, `admit`,",
        "  `axiom`, or `constant`.",
        "- Display names are `first_author_first_three_title_words_year` (underscore",
        "  joined); authors, titles, and years are read from `papers.json`, and an",
        "  unlisted paper falls back to its directory name.",
        "",
        "| No. | Paper | Status | Definition-like items | Theorem-like items |",
        "| ---: | --- | --- | ---: | ---: |",
    ]

    for number, paper in enumerate(papers, start=1):
        finished = paper.open_items == 0
        status_text = "finished" if finished else "in progress"
        status_color = "16a34a" if finished else "f59e0b"
        open_color = "64748b" if paper.open_items == 0 else "dc2626"
        paper_link = quote(paper.path.as_posix(), safe="/")
        status_badge = (
            "![{0}](https://img.shields.io/static/v1?label=&message={1}"
            "&color={2}&style=flat-square)"
        ).format(status_text, quote(status_text), status_color)
        definition_badge = (
            f"![definition-like {paper.definitions}]"
            f"(https://img.shields.io/static/v1?label=&message={paper.definitions}"
            "&color=2563eb&style=flat-square)"
        )
        theorem_badges = (
            f"![proved {paper.proved}]"
            f"(https://img.shields.io/badge/proved-{paper.proved}-16a34a?style=flat-square) "
            f"![open {paper.open_items}]"
            f"(https://img.shields.io/badge/open-{paper.open_items}-{open_color}?style=flat-square)"
        )
        lines.append(
            f"| {number} | [{paper.display_name}]({paper_link}) | {status_badge} | "
            f"{definition_badge} | {theorem_badges} |"
        )

    lines.extend(["", END_MARKER])
    return "\n".join(lines)


def update_readme(generated: str) -> bool:
    original = README.read_text(encoding="utf-8")

    if START_MARKER in original and END_MARKER in original:
        start = original.index(START_MARKER)
        end = original.index(END_MARKER, start) + len(END_MARKER)
        updated = original[:start] + generated + original[end:]
    else:
        heading = "## Formalization Status"
        next_heading = "## Foundation"
        start = original.index(heading) + len(heading)
        end = original.index(next_heading, start)
        updated = original[:start] + "\n\n" + generated + "\n\n" + original[end:]

    if updated == original:
        return False

    README.write_text(updated, encoding="utf-8")
    return True


def render_loc_stats() -> str:
    foundation = count_lean_lines(ROOT / "Foundation")
    theoremlib = count_lean_lines(ROOT / "TheoremLib")
    total = DirectoryStats(
        files=foundation.files + theoremlib.files,
        total=foundation.total + theoremlib.total,
        code=foundation.code + theoremlib.code,
    )

    lines = [
        LOC_START_MARKER,
        "",
        badge("foundation_lines", foundation.total, "0f766e"),
        badge("theoremlib_lines", theoremlib.total, "2563eb"),
        badge("total_lines", total.total, "16a34a"),
        "",
        "Counting convention:",
        "",
        "- `*_lines` counts every line of a `.lean` file, including comments and",
        "  blank lines; the table's `Code lines` column excludes comments,",
        "  docstrings, and blank lines.",
        "- Refreshed automatically after each push to `main`.",
        "",
        "| Directory | `.lean` files | Total lines | Code lines |",
        "| --- | ---: | ---: | ---: |",
        f"| Foundation | {foundation.files} | {foundation.total} | {foundation.code} |",
        f"| TheoremLib | {theoremlib.files} | {theoremlib.total} | {theoremlib.code} |",
        f"| **Total** | **{total.files}** | **{total.total}** | **{total.code}** |",
        "",
        LOC_END_MARKER,
    ]
    return "\n".join(lines)


def update_loc_stats(generated: str) -> bool:
    original = README.read_text(encoding="utf-8")

    if LOC_START_MARKER in original and LOC_END_MARKER in original:
        start = original.index(LOC_START_MARKER)
        end = original.index(LOC_END_MARKER, start) + len(LOC_END_MARKER)
        updated = original[:start] + generated + original[end:]
    else:
        section = f"## Code Statistics\n\n{generated}\n\n"
        next_heading = "## Foundation"
        position = original.find(next_heading)
        if position == -1:
            updated = original.rstrip("\n") + "\n\n" + section
        else:
            updated = original[:position] + section + original[position:]

    if updated == original:
        return False

    README.write_text(updated, encoding="utf-8")
    return True


def main() -> None:
    papers = collect_papers()
    changed = update_readme(render_status(papers))
    changed = update_loc_stats(render_loc_stats()) or changed
    state = "updated" if changed else "already up to date"
    print(f"README.md {state}; counted {len(papers)} papers.")


if __name__ == "__main__":
    main()
