#!/usr/bin/env python3
"""BS の複数モジュールを一つのモジュールにまとめるスクリプト（BS-W5 以降）。

計画は JSON：{"merges": {新モジュール名: [元モジュール名, ...]}, "docstrings": {新モジュール名: 本文},
"stubs": [所有範囲外から import される元モジュール名, ...]（省略可）}。
元モジュールは並べた順に連結する（後のものが前のものを import してよい順に並べること）。

まとめ方（宣言・証明・名前空間・variable には手を加えない）：
- 先頭は `module`、元モジュールの `public import` の和（同じ統合先に入るモジュールと自分自身は除き、
  統合された名前は新しい名前に置き換えて重複を除く）、計画の docstring、元の universe 宣言の和。
- 各元モジュールは `/-! ## 見出し（旧 パス） ... -/` の後、元の冒頭の section 行（`@[expose] public noncomputable section`・
  `@[expose] public section`・`public section` など）に元ファイル名を付けた名前付き section で包み、`end 元ファイル名` で閉じる。
  修飾子（公開・expose・noncomputable）の効果は section ごとに効くので、元のファイルと同じ意味が保たれる。
  見出しの下には元の module docstring の本文をそのまま残す。variable・set_option・open は section の中に閉じる。
  section 行のない元モジュール（import と docstring だけの集約）は見出しだけを残す。
- 元ファイルは git rm する（統合先と同じパスのものは上書き）。
- 所有範囲（BS・CLMST・BS/CLMST の監査）の import 行・`let mods` の名前一覧・バッククォートのモジュール名を
  新しい名前に書き換え、重複した import 行と自分自身の import を除く。

- "stubs" に挙げた元モジュールは、git rm の後に旧名の位置へ転送スタブ（新しい場所を public import するだけ）を書く。
  所有範囲外の import 元がすべて stubs に入っていなければ止まる。

既定は dry-run。--apply で書き込みと git rm を行う。コミット・ビルドはしない。
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNED = [
    re.compile(r"^SerrePositivity/BhattScholze/.*\.lean$"),
    re.compile(r"^SerrePositivity/CLMST/.*\.lean$"),
    re.compile(r"^SerrePositivity/Inputs/Perfectoidization\.lean$"),
    re.compile(r"^scripts/audit_bhatt_scholze[^/]*\.lean$"),
    re.compile(r"^scripts/audit_clmst[^/]*\.lean$"),
    re.compile(r"^scripts/audit_andre_[^/]*\.lean$"),
    re.compile(r"^scripts/audit/bhatt_scholze\.lean$"),
    re.compile(r"^scripts/audit/clmst\.lean$"),
    # CommutativeAlgebra のうち BS・CLMST だけが使う 4 本（BS-W4 で確認済み）
    re.compile(r"^SerrePositivity/CommutativeAlgebra/(AbsolutelyIntegrallyClosedPerfectoidQuotient|PerfectoidIdeal|"
               r"PerfectoidIdealCompatibleRoots|PerfectoidIdealCover)\.lean$"),
]
NAME = re.compile(r"(?<![\w.])SerrePositivity\.BhattScholze\.[\w.']+")
IMPORT = re.compile(r"^[ \t]*(public[ \t]+)?import[ \t]+(\S+)[ \t]*$")
STUB = """module

public import {new}

/-! # 互換用の転送モジュール

## 概要
このモジュールの本体は `{new}` へ統合した。

## 方針
所有範囲外のファイルが旧名で import しているため、旧名を残して新しい場所を再公開する。宣言は持たない。

## 使われ方
旧名の import 元が新しい名前へ切り替わったら削除する。
-/
"""
HEADER = re.compile(r"^(@\[expose\] )?public (noncomputable )?section\s*$")
UNIVERSE = re.compile(r"^universe\s+(.*)$")


def to_path(mod):
    return ROOT / (mod.replace(".", "/") + ".lean")


def parse(mod):
    lines = to_path(mod).read_text().splitlines()
    imports, doc, i = [], None, 0
    while i < len(lines) and not HEADER.match(lines[i]):
        m = IMPORT.match(lines[i])
        if m:
            imports.append(m.group(2))
        elif lines[i].startswith("/-!"):
            j = i
            while "-/" not in lines[j]:
                j += 1
            doc = "\n".join(lines[i:j + 1])
            i = j
        i += 1
    if i >= len(lines):
        return imports, doc, [], None, None
    header = lines[i].strip()
    i += 1
    universes = []
    while i < len(lines) and (UNIVERSE.match(lines[i]) or not lines[i].strip()):
        m = UNIVERSE.match(lines[i])
        if m:
            universes += m.group(1).split()
        i += 1
    # section 行の直後以外（open や set_option の後など）にある universe 宣言も冒頭へ集める。
    # 統合先の冒頭で和を宣言するので、本文に残すと同名の宇宙変数の二重宣言になる（BS-W6 の失敗）。
    rest = []
    for line in lines[i:]:
        m = UNIVERSE.match(line)
        if m:
            universes += [u for u in m.group(1).split() if u not in universes]
        else:
            rest.append(line)
    return imports, doc, universes, header, "\n".join(rest).rstrip() + "\n"


def part_heading(mod, doc):
    rel = mod.replace("SerrePositivity.BhattScholze.", "").replace(".", "/") + ".lean"
    if doc is None:
        return f"/-! ## {mod.split('.')[-1]}（旧 {rel}） -/"
    body = doc[3:-2].strip("\n")
    lines = body.splitlines()
    title = lines[0].lstrip("# ").strip() if lines and lines[0].lstrip().startswith("#") else mod.split(".")[-1]
    rest = "\n".join(lines[1:]).strip("\n")
    return f"/-! ## {title}（旧 {rel}）\n\n{rest}\n-/" if rest else f"/-! ## {title}（旧 {rel}） -/"


def build(new, parts, rename, docstring):
    imports, universes, chunks = [], [], []
    for mod in parts:
        imps, doc, unis, header, body = parse(mod)
        for imp in imps:
            imp2 = rename.get(imp, imp)
            if imp2 != new and imp2 not in imports:
                imports.append(imp2)
        for u in unis:
            if u not in universes:
                universes.append(u)
        stem = mod.split(".")[-1]
        if header is None:
            chunks.append(f"{part_heading(mod, doc)}\n")
        else:
            chunks.append(f"{part_heading(mod, doc)}\n\n{header} {stem}\n\n{body}\nend {stem}\n")
    head = "module\n\n" + "".join(f"public import {i}\n" for i in imports)
    head += f"\n/-!\n{docstring.strip()}\n-/\n"
    if universes:
        head += f"\nuniverse {' '.join(universes)}\n"
    return head + "\n" + "\n".join(chunks)


def listed_files():
    out = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT).decode()
    return sorted(f for f in out.split("\0") if f)


def rewrite(src, rename, self_mod):
    out, seen = [], set()
    for line in src.splitlines():
        m = IMPORT.match(line)
        if m:
            new = rename.get(m.group(2), m.group(2))
            if new == self_mod or (m.group(1) or "", new) in seen:
                continue
            seen.add((m.group(1) or "", new))
            out.append(line.replace(m.group(2), new))
        else:
            out.append(NAME.sub(lambda k: rename.get(k.group(0), k.group(0)), line))
    return "\n".join(out) + ("\n" if src.endswith("\n") else "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("plan", type=Path)
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    plan = json.loads(args.plan.read_text())
    merges, docs = plan["merges"], plan["docstrings"]
    stubs = set(plan.get("stubs", []))
    rename = {old: new for new, olds in merges.items() for old in olds}
    # 統合先と同じ名前の元モジュールはそのまま残るのでスタブは不要。スタブにすると統合した本文を上書きする（BS-W7 の適用前の指摘）。
    assert not (stubs & set(merges)), f"merge targets listed as stubs: {sorted(stubs & set(merges))}"
    assert stubs <= set(rename), f"stubs that are not merged: {sorted(stubs - set(rename))}"
    for new, olds in merges.items():
        assert new in docs, f"docstring missing for {new}"
        for old in olds:
            assert to_path(old).is_file(), f"missing source {old}"
        assert not to_path(new).exists() or new in olds, f"destination exists {new}"
    built = {new: build(new, olds, rename, docs[new]) for new, olds in merges.items()}
    removed = sorted({old for olds in merges.values() for old in olds} - set(merges))
    edits = {}
    for f in listed_files():
        if not f.endswith(".lean") or not any(r.match(f) for r in OWNED) or not (ROOT / f).is_file():
            continue
        mod = "SerrePositivity." + f[len("SerrePositivity/"):-5].replace("/", ".") \
            if f.startswith("SerrePositivity/") else None
        if mod in rename:
            continue
        src = (ROOT / f).read_text()
        new = rewrite(src, rename, mod)
        if new != src:
            edits[f] = new
    foreign, unstubbed = [], set()
    for f in listed_files():
        if not f.endswith(".lean") or not (ROOT / f).is_file() or any(r.match(f) for r in OWNED):
            continue
        hit = {o for o in rename if rename[o] != o
               and re.search(rf"import\s+{re.escape(o)}\s*$", (ROOT / f).read_text(), re.M)}
        if hit:
            foreign.append(f)
            unstubbed |= hit - stubs
    print(json.dumps({
        "new_modules": {n: len(o) for n, o in merges.items()},
        "removed_files": len(removed),
        "lines": {n: built[n].count("\n") for n in built},
        "owned_files_rewritten": len(edits),
        "foreign_importers": foreign,
        "stubs": sorted(stubs),
        "foreign_imports_without_stub": sorted(unstubbed),
        "applied": args.apply,
    }, ensure_ascii=False, indent=1))
    if unstubbed:
        raise SystemExit("foreign importers would break: add these modules to stubs")
    if not args.apply:
        return
    for new, text in built.items():
        to_path(new).write_text(text)
    for old in removed:
        subprocess.run(["git", "rm", "-q", "--", str(to_path(old).relative_to(ROOT))],
                       cwd=ROOT, check=True)
    for f, text in edits.items():
        (ROOT / f).write_text(text)
    for old in sorted(stubs):
        to_path(old).write_text(STUB.format(new=rename[old]))


if __name__ == "__main__":
    main()
