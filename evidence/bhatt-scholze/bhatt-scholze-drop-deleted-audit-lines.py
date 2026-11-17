#!/usr/bin/env python3
"""BS-W8 の作業 C：削除したモジュールの宣言を調べる監査の行を外す。

計画（bhatt-scholze-codex-w8-merges.json）の "deletes" と監査ファイルを引数に取る。各監査について
(1) `let mods` などの名前一覧（バッククォートの名前）から削除したモジュール名を外し、
(2) `lake env lean -DmaxErrors=100000` を実行して `Unknown constant`・`Unknown identifier` のエラーになった名前を集め、
    その名前を最後の語とする `assert_no_sorry`・`#print axioms`・`#print sorries` の行を消す。
(2) は未知名がなくなるまでくり返す。消した名前は /tmp/bs_w8_removed_names.txt に追記する。
未知名以外のエラーが残れば、そのまま止まって報告する（直さない）。
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
plan = json.loads(Path(sys.argv[1]).read_text())
deletes = set(plan["deletes"])
UNKNOWN = re.compile(r"error(?:\([^)]*\))?: [Uu]nknown (?:constant|identifier) [`'‘](../../formalization-plans/bhatt-scholze/[^`'’]+)[`'’]")
ERROR = re.compile(r":\d+:\d+: error")
removed_all = []
LOG = Path("/tmp/bs_w8_removed_names.txt")
for audit in sys.argv[2:]:
    path = ROOT / audit
    text = path.read_text()
    for d in deletes:
        text = re.sub(rf",?\s*`{re.escape(d)}(?![\w.'])", "", text)
    text = text.replace("[,", "[").replace("[\n,", "[\n")
    path.write_text(text)
    for round_ in range(20):
        out = subprocess.run(["lake", "env", "lean", "-DmaxErrors=100000", audit], cwd=ROOT,
                             capture_output=True, text=True).stdout
        names = sorted(set(UNKNOWN.findall(out)))
        others = [l for l in out.splitlines() if ERROR.search(l) and not UNKNOWN.search(l)]
        if not names:
            print(json.dumps({"audit": audit, "rounds": round_, "other_errors": others[:10]}, ensure_ascii=False))
            if others:
                raise SystemExit("errors other than unknown names remain")
            break
        lines = path.read_text().splitlines(keepends=True)
        keep = []
        for l in lines:
            m = re.match(r"^\s*(assert_no_sorry|#print axioms|#print sorries)\s+(\S+)\s*$", l)
            if m and any(m.group(2) == n or m.group(2).endswith("." + n) or n.endswith("." + m.group(2)) for n in names):
                continue
            keep.append(l)
        if len(keep) == len(lines):
            raise SystemExit(f"{audit}: unknown names but no matching lines: {names[:10]}")
        path.write_text("".join(keep))
        removed_all += names
        with LOG.open("a") as fh:
            fh.write("".join(n + "\n" for n in names))
print(json.dumps({"removed_names": len(set(removed_all))}))
