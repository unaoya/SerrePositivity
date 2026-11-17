#!/usr/bin/env python3
"""文書の移動表（formalization-plans/doc-reorg/move-table.csv）を適用する。

使い方: python3 scripts/docs/apply_move_table.py [--when PREFIX] [--dry-run]
  --when PREFIX  列 when がこの接頭辞で始まる行だけを適用する（既定「すぐ」）。
  --dry-run      git mv と書き換えをせず、件数だけ出す。

やること（リポジトリの根で実行する）:
  1. 行ごとに git mv src → dst（src は formalization-plans/ からの相対、dst は
     formalization-plans/ からの相対か、evidence/ で始まる根からの相対）。
  2. リポジトリの文書（md・html・py・sh・tex・csv・txt・toml、.lean と .lake は除く）の
     相対リンク（markdown の ](…)、html の href/src）を、移動前の場所で解決してから
     移動後の場所に合わせて書き直す。移動した文書の中のリンクも同じ規則で直す。
  3. 根からの絶対な書き方（`formalization-plans/<src>`）を新しいパスに置き換える。
  4. formalization-plans の文書の中のバッククォートの `<src>` を `<dst>` に置き換える。
  5. .lean に残る参照と、置き換えられなかったバッククォートの参照を一覧にする。
検証の証拠のディレクトリの中身（json・gz・log）は書き換えない。
"""
import argparse
import csv
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
PLANS = "formalization-plans"
TABLE = ROOT / PLANS / "doc-reorg" / "move-table.csv"
TEXT_SUFFIXES = {".md", ".html", ".py", ".sh", ".tex", ".csv", ".txt", ".toml"}
SKIP_DIRS = {".lake", ".git", "node_modules", "_out"}


def full(rel: str) -> str:
    rel = rel.rstrip("/")
    return rel if rel.startswith("evidence/") else f"{PLANS}/{rel}"


def load_moves(when_prefix):
    moves = []
    with open(TABLE, newline="") as f:
        for r in csv.DictReader(f):
            if not r["when"].startswith(when_prefix):
                continue
            src, dst = full(r["src"]), full(r["dst"])
            if src == dst or dst.endswith("?"):
                continue
            moves.append((src, dst))
    return moves


def is_evidence_payload(path: pathlib.Path, moved_dirs) -> bool:
    rel = path.as_posix()
    return any(rel.startswith(d + "/") for d in moved_dirs if d.startswith("evidence/")) and path.suffix not in {".md", ".html", ".py", ".sh"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--when", default="すぐ")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    os.chdir(ROOT)

    moves = load_moves(args.when)
    file_map, dir_map = {}, {}
    for src, dst in moves:
        if (ROOT / src).is_dir():
            dir_map[src] = dst
        elif (ROOT / src).exists():
            file_map[src] = dst
        else:
            print(f"missing: {src}", file=sys.stderr)
    print(f"{len(file_map)} files, {len(dir_map)} directories to move")

    def map_path(p: str) -> str:
        if p in file_map:
            return file_map[p]
        for d, nd in dir_map.items():
            if p == d or p.startswith(d + "/"):
                return nd + p[len(d):]
        return p

    # すべての文書の「移動前の場所」を記録してから動かす
    docs = []
    for path in ROOT.rglob("*"):
        if not path.is_file() or path.suffix not in TEXT_SUFFIXES:
            continue
        rel = path.relative_to(ROOT).as_posix()
        if any(part in SKIP_DIRS for part in path.relative_to(ROOT).parts):
            continue
        if is_evidence_payload(path.relative_to(ROOT), set(dir_map.values()) | {map_path(s) for s in dir_map}):
            continue
        docs.append(rel)

    if args.dry_run:
        print("dry run: no changes")
    else:
        for src, dst in list(file_map.items()) + list(dir_map.items()):
            (ROOT / dst).parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "mv", src, dst], check=True)

    link_md = re.compile(r"(?<!\w)(\[[^\]\n]*\]\()([^)\s]+)(\))")
    link_html = re.compile(r'((?:href|src)=")([^"]+)(")')
    abs_pat = re.compile(r"formalization-plans/([A-Za-z0-9_./-]+)")
    tick_pat = re.compile(r"`((?:stage-ii|bhatt-scholze|infinity-lanes|kst-lanes)/[A-Za-z0-9_./-]+|[A-Za-z0-9_-]+\.md)`")
    plan_old_rel = {s: s[len(PLANS) + 1:] for s in list(file_map) + list(dir_map)}

    changed = 0
    leftovers = []
    for old_rel in docs:
        new_rel = map_path(old_rel)
        path = ROOT / (old_rel if args.dry_run else new_rel)
        try:
            text = path.read_text()
        except UnicodeDecodeError:
            continue
        old_dir = pathlib.PurePosixPath(old_rel).parent
        new_dir = pathlib.PurePosixPath(new_rel).parent

        def fix_link(m):
            head, target, tail = m.group(1), m.group(2), m.group(3)
            if re.match(r"[a-zA-Z]+:|#|mailto:|/", target):
                return m.group(0)
            t, frag = (target.split("#", 1) + [""])[:2]
            t = t.strip("<>")
            if not t:
                return m.group(0)
            abs_old = os.path.normpath((old_dir / t).as_posix())
            if abs_old.startswith(".."):
                return m.group(0)
            abs_new = map_path(abs_old)
            if abs_new == abs_old and new_dir == old_dir:
                return m.group(0)
            rel_new = os.path.relpath(abs_new, new_dir.as_posix() or ".")
            if (ROOT / abs_new).is_dir() and target.rstrip("#").endswith("/"):
                rel_new += "/"
            return f"{head}{rel_new}{'#' + frag if frag else ''}{tail}"

        new_text = link_md.sub(fix_link, text)
        if path.suffix == ".html":
            new_text = link_html.sub(fix_link, new_text)

        def fix_abs(m):
            p = f"{PLANS}/{m.group(1)}"
            stripped = p.rstrip("/.")
            return map_path(stripped) + p[len(stripped):]

        new_text = abs_pat.sub(fix_abs, new_text)

        if new_rel.startswith(PLANS + "/"):
            def fix_tick(m):
                inner = m.group(1)
                for s, s_rel in plan_old_rel.items():
                    if inner == s_rel or inner.startswith(s_rel + "/") or (s_rel.count("/") == 0 and inner == s_rel):
                        new = map_path(s) + inner[len(s_rel):]
                        if new.startswith(PLANS + "/"):
                            new = new[len(PLANS) + 1:]
                        return f"`{new}`"
                return m.group(0)
            new_text = tick_pat.sub(fix_tick, new_text)

        if new_text != text:
            changed += 1
            if not args.dry_run:
                path.write_text(new_text)
    print(f"{changed} documents rewritten")

    # 残る参照
    basenames = {pathlib.PurePosixPath(s).name for s in list(file_map) + list(dir_map)}
    pat = "|".join(re.escape(b) for b in sorted(basenames))
    out = subprocess.run(["rg", "-n", "-e", pat, "--glob", "*.lean", "SerrePositivity", "scripts"],
                         capture_output=True, text=True).stdout
    print("--- .lean references (not rewritten):")
    print(out.strip() or "(none)")


if __name__ == "__main__":
    main()
