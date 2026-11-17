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

- "deletes"（省略可）に挙げたモジュールは git rm する（BS-W8 から）。削除しないモジュールのうち所有範囲の Lean ファイルが
  それを import していれば、監査（scripts/）の import 行だけは外し、それ以外は止まる。監査の中の宣言名の行は Codex が別途消す。
- "private_renames"（省略可、{元モジュール名: {旧名: 新名}}）：同じ統合先に同名の private 宣言が二つあると二重宣言になるので、
  指定した元モジュールの本文の中だけで、その名前を単語単位で置き換える（BS-W8 から）。
- "stubs" に挙げた元モジュールは、git rm の後に旧名の位置へ転送スタブ（新しい場所を public import するだけ）を書く。
  所有範囲外の import 元がすべて stubs に入っていなければ止まる。

既定は dry-run。--apply で書き込みと git rm を行う。コミット・ビルドはしない。
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OWNED = [
    re.compile(r"^SerrePositivity/BhattScholze/.*\.lean$"),
    re.compile(r"^SerrePositivity/CLMST/.*\.lean$"),
    re.compile(r"^SerrePositivity/Inputs/Perfectoidization\.lean$"),
    re.compile(r"^scripts/audit_bhatt_scholze[^/]*\.lean$"),
    re.compile(r"^scripts/audit_clmst[^/]*\.lean$"),
    re.compile(r"^scripts/audit_andre_[^/]*\.lean$"),
    re.compile(r"^scripts/audit/bhatt_scholze\.lean$"),
    re.compile(r"^scripts/audit/clmst\.lean$"),
    # BS の集約（BS-W8a で作成）。統合で名前が変わったときはここだけを直す
    re.compile(r"^SerrePositivity/BhattScholze\.lean$"),
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
    imports, doc, i, pre = [], None, 0, []
    while i < len(lines) and not HEADER.match(lines[i]):
        m = IMPORT.match(lines[i])
        if m:
            imports.append(m.group(2))
        elif lines[i].strip() and lines[i].strip() != "module" and not lines[i].startswith(("/-!", "--")):
            # section 行より前の open・set_option など（BS-W8 の試験で `Transfinite/BoundedCompletion` の open が落ちた）
            pre.append(lines[i])
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
    for line in pre:
        m = UNIVERSE.match(line)
        if m:
            universes += [u for u in m.group(1).split() if u not in universes]
    pre = [line for line in pre if not UNIVERSE.match(line)]
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
    return imports, doc, universes, header, "\n".join(pre + rest).rstrip() + "\n"


SCOPE_OPEN = re.compile(r"^\s*(?:@\[expose\]\s+)?(?:public\s+)?(?:noncomputable\s+)?(?:meta\s+)?(namespace|section)\b\s*(\S*)")
SCOPE_END = re.compile(r"^\s*end\b\s*(\S*)")


def unclosed_anonymous(body, mod):
    stack = []
    for line in body.splitlines():
        m = SCOPE_OPEN.match(line)
        if m:
            stack.append(m.group(2))
            continue
        e = SCOPE_END.match(line)
        if e and stack:
            stack.pop()
    assert all(name == "" for name in stack), f"named scope left open in {mod}: {stack}"
    return len(stack)


def part_heading(mod, doc):
    rel = mod.replace("SerrePositivity.BhattScholze.", "").replace(".", "/") + ".lean"
    if doc is None:
        return f"/-! ## {mod.split('.')[-1]}（旧 {rel}） -/"
    body = doc[3:-2].strip("\n")
    lines = body.splitlines()
    title = lines[0].lstrip("# ").strip() if lines and lines[0].lstrip().startswith("#") else mod.split(".")[-1]
    rest = "\n".join(lines[1:]).strip("\n")
    return f"/-! ## {title}（旧 {rel}）\n\n{rest}\n-/" if rest else f"/-! ## {title}（旧 {rel}） -/"


def build(new, parts, rename, docstring, privs=None):
    imports, universes, chunks = [], [], []
    for mod in parts:
        imps, doc, unis, header, body = parse(mod)
        for old, nw in (privs or {}).get(mod, {}).items():
            body, k = re.subn(rf"(?<![\w.']){re.escape(old)}(?![\w'])", nw, body)
            assert k > 0, f"private rename not found: {mod} {old}"
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
            # 本文の中で開いたまま終わる無名の section（例：`noncomputable section`）は、ファイル末尾では暗黙に閉じるが、
            # 名前付き section で包むと `end 元ファイル名` と合わなくなるので、ここで閉じる（BS-W8 で確認）。
            closers = "".join("end\n" for _ in range(unclosed_anonymous(body, mod)))
            chunks.append(f"{part_heading(mod, doc)}\n\n{header} {stem}\n\n{body}{closers}\nend {stem}\n")
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
    ap.add_argument("--write-missing-stubs", action="store_true",
                    help="部分適用からの復旧用：--apply の後、まだ書かれていないスタブだけを書く（他は何もしない）")
    args = ap.parse_args()
    plan = json.loads(args.plan.read_text())
    merges, docs = plan["merges"], plan["docstrings"]
    stubs = set(plan.get("stubs", []))
    if args.write_missing_stubs:
        rename = {old: new for new, olds in merges.items() for old in olds}
        written = []
        for old in sorted(stubs):
            assert to_path(rename[old]).is_file(), f"merge target missing: {rename[old]}"
            if not to_path(old).exists():
                to_path(old).parent.mkdir(parents=True, exist_ok=True)
                to_path(old).write_text(STUB.format(new=rename[old]))
                written.append(old)
        print(json.dumps({"stubs_written": len(written), "stubs_total": len(stubs)}, indent=1))
        return
    rename = {old: new for new, olds in merges.items() for old in olds}
    # 統合先と同じ名前の元モジュールはそのまま残るのでスタブは不要。スタブにすると統合した本文を上書きする（BS-W7 の適用前の指摘）。
    assert not (stubs & set(merges)), f"merge targets listed as stubs: {sorted(stubs & set(merges))}"
    assert stubs <= set(rename), f"stubs that are not merged: {sorted(stubs - set(rename))}"
    for new, olds in merges.items():
        assert new in docs, f"docstring missing for {new}"
        for old in olds:
            assert to_path(old).is_file(), f"missing source {old}"
        assert not to_path(new).exists() or new in olds, f"destination exists {new}"
    privs = plan.get("private_renames", {})
    assert set(privs) <= set(rename), f"private_renames outside merges: {sorted(set(privs) - set(rename))}"
    deletes = set(plan.get("deletes", []))
    assert not (deletes & set(rename)), f"deleted modules also merged: {sorted(deletes & set(rename))}"
    for d in deletes:
        assert to_path(d).is_file(), f"missing deleted module {d}"
    built = {new: build(new, olds, rename, docs[new], privs) for new, olds in merges.items()}
    removed = sorted(({old for olds in merges.values() for old in olds} - set(merges)) | deletes)
    audit_unimports, blocked = {}, []
    for f in listed_files():
        if not f.endswith(".lean") or not (ROOT / f).is_file():
            continue
        mod = "SerrePositivity." + f[len("SerrePositivity/"):-5].replace("/", ".") \
            if f.startswith("SerrePositivity/") else None
        if mod in deletes or mod in rename:
            continue
        imported = {m.group(2) for m in map(IMPORT.match, (ROOT / f).read_text().splitlines()) if m}
        hit = sorted(imported & deletes)
        if hit:
            if f.startswith("scripts/") and any(r.match(f) for r in OWNED):
                audit_unimports[f] = hit
            else:
                blocked.append((f, hit))
    if blocked:
        raise SystemExit(f"deleted modules still imported: {blocked}")
    edits = {}
    for f in listed_files():
        if not f.endswith(".lean") or not any(r.match(f) for r in OWNED) or not (ROOT / f).is_file():
            continue
        mod = "SerrePositivity." + f[len("SerrePositivity/"):-5].replace("/", ".") \
            if f.startswith("SerrePositivity/") else None
        if mod in rename or mod in deletes:
            continue
        src = orig = (ROOT / f).read_text()
        if f in audit_unimports:
            src = "".join(l for l in src.splitlines(keepends=True)
                          if not (IMPORT.match(l.rstrip("\n")) and IMPORT.match(l.rstrip("\n")).group(2) in deletes))
        new = rewrite(src, rename, mod)
        # import 行を外しただけのファイルも書き戻す（BS-W8 で audit_bhatt_scholze_andre_conditional の import が残った）
        if new != orig:
            edits[f] = new
    foreign, unstubbed = [], set()
    for f in listed_files():
        if not f.endswith(".lean") or not (ROOT / f).is_file() or any(r.match(f) for r in OWNED):
            continue
        imported = {m.group(2) for m in map(IMPORT.match, (ROOT / f).read_text().splitlines()) if m}
        hit = {o for o in imported if o in rename and rename[o] != o}
        if hit:
            foreign.append(f)
            unstubbed |= hit - stubs
    print(json.dumps({
        "new_modules": {n: len(o) for n, o in merges.items()},
        "removed_files": len(removed),
        "lines": {n: built[n].count("\n") for n in built},
        "owned_files_rewritten": len(edits),
        "deleted": len(deletes),
        "audits_unimporting_deleted": {f: len(h) for f, h in audit_unimports.items()},
        "private_renames": sum(len(v) for v in privs.values()),
        "foreign_importers": foreign,
        "stubs": sorted(stubs),
        "foreign_imports_without_stub": sorted(unstubbed),
        "applied": args.apply,
    }, ensure_ascii=False, indent=1))
    if unstubbed:
        raise SystemExit("foreign importers would break: add these modules to stubs")
    if not args.apply:
        return
    # 新しいサブディレクトリ（例：Prism/Bounded/）の統合先にも書けるよう、書き込みの前に親ディレクトリを作る（BS-W7 の失敗）。
    for new in built:
        to_path(new).parent.mkdir(parents=True, exist_ok=True)
    for new, text in built.items():
        to_path(new).write_text(text)
    for old in removed:
        subprocess.run(["git", "rm", "-q", "--", str(to_path(old).relative_to(ROOT))],
                       cwd=ROOT, check=True)
    for f, text in edits.items():
        (ROOT / f).write_text(text)
    # git rm で空になったディレクトリは消えるので、スタブの親ディレクトリも作り直す（BS-W7 の二度目の失敗）。
    for old in sorted(stubs):
        to_path(old).parent.mkdir(parents=True, exist_ok=True)
        to_path(old).write_text(STUB.format(new=rename[old]))


if __name__ == "__main__":
    main()
