#!/usr/bin/env python3
"""items.csv の declarations 列の「名前 @ パス:行」が今の作業木と合うかを調べ、直せるものは直す。

使い方: python3 research/bs-coverage/check_locations.py [--write]
  引数なし：ずれの一覧を出すだけ。--write：一意に決まるものだけ items.csv を書き換える。

判定（名前の最後の成分で探す。名前空間は見ない）:
  - ok      ：書かれた行の前後 2 行に名前がある
  - 行      ：同じファイルに宣言が一つだけある → 行を直す
  - 移動    ：同じファイルにはなく、SerrePositivity/ と drafts/ 全体で宣言が一つだけある → パスと行を直す
              （drafts から本体へ移ったものは status の見直しが要るので、一覧に出す）
  - 未解決  ：見つからない、または候補が複数 → 直さない
"""
import csv
import io
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
ITEMS = ROOT / "research" / "bs-coverage" / "items.csv"
SEARCH = [ROOT / "SerrePositivity", ROOT / "formalization-plans" / "bhatt-scholze" / "drafts"]
DECL = (r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public|nonrec|partial|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+(?:\S+\.)?")

_files = None


def all_files():
    global _files
    if _files is None:
        _files = {}
        for d in SEARCH:
            for p in d.rglob("*.lean"):
                _files[p.relative_to(ROOT).as_posix()] = p.read_text().split("\n")
    return _files


def decl_lines(lines, last):
    pat = re.compile(DECL + re.escape(last) + r"(?=[\s:({\[]|$)")
    return [i + 1 for i, l in enumerate(lines) if pat.search(l)]


def check(name, path, line):
    last = name.split(".")[-1]
    files = all_files()
    lines = files.get(path)
    if lines is not None and line:
        win = "\n".join(lines[max(0, line - 3): line + 2])
        if re.search(r"(?<![\w'])" + re.escape(last) + r"(?![\w'])", win):
            return "ok", path, line
    if lines is not None:
        hits = decl_lines(lines, last)
        if len(hits) == 1:
            return "行", path, hits[0]
    hits = [(p, n) for p, ls in files.items() for n in decl_lines(ls, last)]
    if len(hits) == 1:
        return "移動", hits[0][0], hits[0][1]
    return "未解決", path, line


def main():
    write = "--write" in sys.argv[1:]
    raw = ITEMS.read_text()
    nl = "\r\n" if "\r\n" in raw else "\n"
    rows = list(csv.DictReader(io.StringIO(raw)))
    counts = {}
    for r in rows:
        out = []
        for d in filter(None, (s.strip() for s in r["declarations"].split("|"))):
            m = re.match(r"(.+?) @ (.+?)(?::(\d+))?$", d)
            if not m:
                out.append(d)
                continue
            name, path, line = m.group(1), m.group(2), int(m.group(3) or 0)
            kind, npath, nline = check(name, path, line)
            counts[kind] = counts.get(kind, 0) + 1
            if kind != "ok":
                note = "（drafts → 本体：status を見直す）" if "drafts" in path and "drafts" not in npath else ""
                print(f"{kind}\t{r['number']}\t{name}\t{path}:{line} → {npath}:{nline}{note}")
            if kind in ("行", "移動"):
                out.append(f"{name} @ {npath}:{nline}")
            else:
                out.append(d)
        r["declarations"] = " | ".join(out)
    print("集計：" + "、".join(f"{k} {v}" for k, v in counts.items()))
    if write:
        o = io.StringIO()
        w = csv.DictWriter(o, list(rows[0].keys()), lineterminator=nl)
        w.writeheader()
        w.writerows(rows)
        ITEMS.write_text(o.getvalue())
        print("items.csv を書き換えた")


if __name__ == "__main__":
    main()
