#!/usr/bin/env python3
"""BS のモジュールを移すスクリプト（W1 の apply スクリプトを、計画ファイルを引数に取る形にしたもの）。

計画は JSON（moves・stubs・keep）。第一引数で渡す。W2 以降の移動で使う。
scripts/move_module.py はリポジトリ全体の .lean を書き換えるため、所有範囲外
（root の SerrePositivity.lean、CommutativeAlgebra、他レーンの監査）を変えずに済むよう、
書き換えを BS 所有範囲に限定し、外から import されるモジュールは元の場所に転送スタブを置く。

既定は dry-run（何も変更せず、書き換え対象と件数を表示）。
--apply で git mv と import の書き換えを行う（コミット 3a）。
--stubs で旧名の位置に転送スタブを書く（コミット 3a の後に実行し、コミット 3b にする）。
二段に分けるのは、同じコミットで旧パスにスタブを置くと git が rename を検出できないため。
宣言名・名前空間は一切変えない。コミット・ビルドはしない。
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# 書き換えてよい（BS 作業チャットの所有範囲の）ファイル。
OWNED = [
    re.compile(r"^SerrePositivity/BhattScholze/.*\.lean$"),
    re.compile(r"^SerrePositivity/CLMST/.*\.lean$"),
    re.compile(r"^SerrePositivity/Inputs/Perfectoidization\.lean$"),
    re.compile(r"^scripts/audit_bhatt_scholze[^/]*\.lean$"),
    re.compile(r"^scripts/audit_clmst[^/]*\.lean$"),
    re.compile(r"^scripts/audit_andre_[^/]*\.lean$"),
    re.compile(r"^scripts/audit/bhatt_scholze\.lean$"),
    re.compile(r"^scripts/audit/clmst\.lean$"),
]
# 生成された領域監査は import 行のほかに `let mods` の名前一覧を持つので、モジュール名の字句をすべて置き換える。
NAME_LISTS = {"scripts/audit/bhatt_scholze.lean", "scripts/audit/clmst.lean"}
NAME = re.compile(r"(?<![\w.])SerrePositivity\.BhattScholze\.[\w.']+")
# 監査ファイルの `let modules` やスタブの docstring は、バッククォート付きのモジュール名で旧名を持つ。
BACKTICK = re.compile(r"(?<=`)SerrePositivity\.BhattScholze\.[\w.']+")
IMPORT = re.compile(r"^([ \t]*(?:public[ \t]+)?import[ \t]+)(SerrePositivity\.BhattScholze\.[\w.']+)([ \t]*)$", re.M)

STUB = """module

public import {new}

/-! # 互換用の転送モジュール

## 概要
このモジュールの本体は `{new}` へ移した。

## 方針
所有範囲外のファイル（root の集約や共有の監査）が旧名で import しているため、
旧名を残して新しい場所を再公開する。宣言は持たない。

## 使われ方
旧名の import 元が新しい名前へ切り替わったら削除する。
-/
"""


def to_path(mod):
    return ROOT / (mod.replace(".", "/") + ".lean")


def listed_files():
    out = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT).decode()
    return sorted(f for f in out.split("\0") if f)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("plan", type=Path)
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--stubs", action="store_true")
    args = ap.parse_args()
    plan = json.loads(args.plan.read_text())
    moves, stubs, keep = plan["moves"], set(plan["stubs"]), set(plan["keep"])
    if args.stubs:
        for old in sorted(stubs):
            assert to_path(moves[old]).is_file(), f"run --apply first: {moves[old]}"
            assert not to_path(old).exists(), f"stub path occupied: {old}"
        for old in sorted(stubs):
            to_path(old).write_text(STUB.format(new=moves[old]))
        print(f"wrote {len(stubs)} stubs")
        return
    assert not (set(moves) & keep) and stubs <= set(moves)
    assert len(set(moves.values())) == len(moves)
    for old, new in moves.items():
        assert to_path(old).is_file(), f"missing source {old}"
        assert not to_path(new).exists(), f"destination exists {new}"

    files = listed_files()
    owned = [f for f in files if any(r.match(f) for r in OWNED)]
    edits, foreign = {}, {}
    for f in files:
        if not f.endswith(".lean") or not (ROOT / f).is_file():
            continue
        src = (ROOT / f).read_text()
        hit = [m.group(2) for m in IMPORT.finditer(src) if m.group(2) in moves]
        if f in owned and not hit and any(m.group(0) in moves for m in BACKTICK.finditer(src)):
            edits[f] = BACKTICK.sub(lambda m: moves.get(m.group(0), m.group(0)), src)
            continue
        if f in NAME_LISTS and f in owned:
            new = NAME.sub(lambda m: moves.get(m.group(0), m.group(0)), src)
            if new != src:
                edits[f] = new
            continue
        if not hit:
            continue
        if f in owned:
            new = IMPORT.sub(lambda m: m.group(1) + moves.get(m.group(2), m.group(2)) + m.group(3), src)
            new = BACKTICK.sub(lambda m: moves.get(m.group(0), m.group(0)), new)
            edits[f] = new
        else:
            foreign[f] = sorted(set(hit))
    missing = sorted(set(m for v in foreign.values() for m in v) - stubs)
    print(json.dumps({
        "moves": len(moves), "stubs": len(stubs), "keep": sorted(keep),
        "owned_files_rewritten": len(edits),
        "foreign_importers_left_unchanged": {k: len(v) for k, v in foreign.items()},
        "foreign_imports_without_stub": missing,
        "applied": args.apply,
    }, ensure_ascii=False, indent=1))
    if missing:
        raise SystemExit("foreign importers would break: add these modules to stubs")
    if not args.apply:
        return
    for old, new in moves.items():
        dst = to_path(new)
        dst.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", "--", str(to_path(old).relative_to(ROOT)),
                        str(dst.relative_to(ROOT))], cwd=ROOT, check=True)
    for f, text in edits.items():
        path = ROOT / f
        old_mod = "SerrePositivity." + f[len("SerrePositivity/"):-5].replace("/", ".") \
            if f.startswith("SerrePositivity/") else None
        if old_mod in moves:
            path = to_path(moves[old_mod])
        path.write_text(text)


if __name__ == "__main__":
    main()
