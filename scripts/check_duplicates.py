#!/usr/bin/env python3
"""Inventory normalized Lean file duplicates; compare with a saved Markdown baseline.

Only tracked files are read, from the working tree. This is a lexical candidate
finder, not a proof of declaration equality. No Lean source is changed.
"""

import argparse
from collections import defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SCOPE = "SerrePositivity/InfinityCategories"


def strip_comments(source):
    """Remove nested Lean comments, retaining newlines and string contents."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        ch = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                out.append(" ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif quoted:
            out.append(ch)
            i += 1
            if ch == "\\" and i < len(source):
                out.append(source[i])
                i += 1
            elif ch == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            while i < len(source) and source[i] != "\n":
                i += 1
        else:
            out.append(ch)
            quoted = ch == '"'
            i += 1
    return "".join(out)


def normalize(source):
    source = strip_comments(source)
    lines = [line for line in source.splitlines() if not re.match(
        r"^\s*(?:(?:public\s+)?import\b|namespace\b|end(?:\s+[\w.]+)?\s*$)", line)]
    source = "\n".join(lines)
    # Preserve token boundaries and whitespace inside strings; ignore formatting.
    tokens = re.findall(r'"(?:\\.|[^"\\])*"|[\w\'.]+|[^\s]', source)
    tokens = [t if t.startswith('"') else t.replace("KanSection.", "") for t in tokens]
    return " ".join(tokens), bool(re.search(
        r"\b(?:def|abbrev|lemma|theorem|structure|class|instance|inductive)\b", source))


def inventory(scope):
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--", scope], cwd=ROOT).decode().split("\0")
    groups = defaultdict(list)
    count = 0
    for name in sorted(p for p in paths if p.endswith(".lean")):
        source = (ROOT / name).read_text()
        normalized, substantive = normalize(source)
        digest = hashlib.sha256(normalized.encode()).hexdigest()
        groups[(substantive, digest)].append((name, len(source.splitlines())))
        count += 1
    return count, [(body, digest, files) for (body, digest), files in sorted(groups.items())
                   if len(files) > 1]


def duplicate_pairs(groups):
    return sorted([a[0], b[0]] for body, _, files in groups if body
                  for a, b in itertools.combinations(files, 2))


def report(scope, count, groups):
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().strip()
    body = [g for g in groups if g[0]]
    lines = ["# 正規化ハッシュによる重複一覧", "",
             f"- 基準 HEAD: `{revision}`（追跡済みファイルの作業ツリー）。",
             f"- 対象: `{scope}`、{count} Lean ファイル。未追跡ファイルは除外。",
             "- 正規化: コメント（入れ子を含む）、import 行、namespace/end 行を除き、",
             "  文字列外の空白をトークン区切りに統一し、`KanSection.` 修飾を除く。",
             "- 名前空間・import を無視する候補検出であり、型・証明の同一性は変更前に個別確認する。",
             f"- 実体の重複: {len(body)} 群、余分なコピー {sum(len(g[2])-1 for g in body)} 本。",
             f"- 宣言を持たない一致: {len(groups)-len(body)} 群（集約・シム等、実体の重複には数えない）。", ""]
    for substantive, digest, files in sorted(groups, key=lambda g: (not g[0], g[2][0][0])):
        lines += [f"## {'実体' if substantive else '宣言なし'} `{digest}`", ""]
        lines += [f"- `{name}` ({size} 行)" for name, size in files]
        lines.append("")
    lines += ["<!-- duplicate-pairs-v1", json.dumps(duplicate_pairs(groups), ensure_ascii=False), "-->", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope", default=DEFAULT_SCOPE, help="repository-relative directory")
    parser.add_argument("--output", type=Path, help="save full Markdown inventory")
    parser.add_argument("--baseline", type=Path, help="fail on new substantive duplicate pairs")
    args = parser.parse_args()
    count, groups = inventory(args.scope)
    result = report(args.scope, count, groups)
    if args.output:
        args.output.write_text(result)
    if args.baseline:
        match = re.search(r"<!-- duplicate-pairs-v1\n(.*?)\n-->", args.baseline.read_text(), re.S)
        if not match:
            parser.error("baseline lacks duplicate-pairs-v1 data")
        old = {tuple(pair) for pair in json.loads(match[1])}
        added = [pair for pair in duplicate_pairs(groups) if tuple(pair) not in old]
        print(f"Scanned {count} files; new duplicate pairs: {len(added)}")
        for a, b in added:
            print(f"  {a} <-> {b}")
        return bool(added)
    if not args.output:
        print(result, end="")
    else:
        print(f"Saved {args.output}: {count} files, {sum(g[0] for g in groups)} substantive groups")
    return False


if __name__ == "__main__":
    raise SystemExit(main())
