"""全件runの完了と集計の整合を検証し、数学的不存在と名前解決失敗を区別して報告。"""
import collections
import csv
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
RUN = BASE / 'runs/all-20261107-01'
csv.field_size_limit(64 * 1024 * 1024)
plan = json.loads((RUN / 'plan.json').read_text())
summary = json.loads((RUN / 'summary.json').read_text())
with (RUN / 'declaration-results.csv').open() as f:
    refs = list(csv.DictReader(f))
with (RUN / 'item-results.csv').open() as f:
    items = list(csv.DictReader(f))
modules = []
for job in plan['jobs']:
    m = json.loads((RUN / 'modules' / job['module'] / 'execution.json').read_text())
    assert m['state'] == 'checked' and m['build_returncode'] == 0
    assert m['lean_returncode'] in (0, 1)
    modules.append(m)
assert len(modules) == 1144
assert len(refs) == len(plan['references']) == 2108
assert len(items) == len(plan['items']) == 3553
assert [r['number'] for r in items] == [r['number'] for r in plan['items']]
assert len({r['id'] for r in refs}) == 2108
assert dict(collections.Counter(r['state'] for r in refs)) == summary['references']
assert dict(collections.Counter(r['state'] for r in items)) == summary['items']
assert all(r['state'] in {'found','not_found','check_failed','unresolved_reference'} for r in refs)
assert sum(r['state'] != 'unresolved_reference' for r in refs) == 1997
assert all(json.loads(r['axioms_json']) is not None for r in refs if r['state'] == 'found')
extra = [r for r in refs if json.loads(r['extra_axioms_json'])]
flags = [r for r in refs if 'ModelCategory' in r['type']]
assert len(extra) == summary['nonstandard_axiom_references']

def save_csv(path, rows, fields):
    with path.open('w', newline='') as f:
        w = csv.DictWriter(f, fields, extrasaction='ignore', lineterminator='\n')
        w.writeheader(); w.writerows(rows)

save_csv(RUN / 'module-results.csv', modules, ['module','state','build_returncode','lean_returncode','started','finished','source_sha256'])
save_csv(RUN / 'model-category-flags.csv', flags, ['id','declaration','source','state','type'])
save_csv(RUN / 'extra-axioms.csv', extra, ['id','declaration','source','state','axioms_json','extra_axioms_json'])
text = '''# 段1・全件検査の完了報告（2026-11-07 JST）

作業枝research/kerodon-review-a。対象はitems.csv全3,553項目の宣言欄。
生出力と最終集計はruns/all-20261107-01/に保存した。

## 全件の実行

- 宣言欄の記載2,880出現を収録。重複を除いた記載は2,108件。
- 実行可能な形式の1,997件について、出典の1,144モジュールを個別にlake buildした後、#check @名前と#print axiomsを実行。
- 全1,144モジュールの準備ビルドは成功。未実行モジュール・ビルド失敗・出力解析不能は0。
- 略記・匿名instanceの説明・省略パス等の111件はunresolved_referenceとして記録し、段2で名前解決する。
- 既存の全体ビルドやverifyは実行していない。ビルドロック競合時は再試行した。

## 原記載どおりの名前による結果

| 状態 | 重複を除いた記載数 |
| --- | ---: |
'''
for state, count in summary['references'].items():
    text += f'| {state} | {count} |\n'
text += '''
foundは型と公理の両方を確認したもの。not_foundは指定されたimportで原記載の名前が解決しなかったもの。
**数学的な内容が存在しないという判定ではない。** 名前空間の不足、移動後の名前のずれ、記法・射影の扱いなどを段2で解決する必要がある。
例えばPiZeroConstant.homEquivはSerrePositivity.SimplicialModel.PiZeroConstant.homEquiv、
SimplicialObjectはCategoryTheory.SimplicialObjectが正しい。Ch1では補正後の別runで実在を確認した。
本集計はitems.csvを変更せず原記載を検査した集計であり、Ch1の補正結果を混ぜていない。

check_failedの1件はFunctor.const。修飾が不足しており、別のconstへのフィールド記法として解釈されるエラーになった。
CategoryTheory.Functor.constへの補正後の成功はCh1の証拠に保存済み。

## 公理と型の仮定

'''
text += f'found {summary["references"]["found"]}件で標準3公理（propext、Classical.choice、Quot.sound）以外は{len(extra)}件。sorryAxの検出も0件。\n'
text += f'取得できた型のModelCategory文字列による抽出は{len(flags)}件。該当一覧はmodel-category-flags.csv。\n'
text += '''名前解決できなかった宣言と未解決記載について、公理や仮定の健全性を承認したという意味ではない。
この段は各主張の仮定が数学的に妥当かを精査する段2とは別であり、ModelCategory以外の強すぎる型クラス仮定も段2で確認する。

## 項目単位の集計

'''
for state, count in summary['items'].items():
    text += f'- {state}: {count}\n'
text += '''
no_declarationsは宣言欄が空の項目であり「確認済み・なし」ではない。
none 1,947項目のうち66項目には関連宣言の記載があり、それも検査対象に含めた。
全項目の番号・順序・重複なしと、集計が元計画に一致することを検証した。

## 保存物と再解析

- plan.json・references.csv・unresolved.csv・inventory.json：全件計画、原記載との対応、未解決記載。
- modules/<Module>/：検査用Lean、コマンド行番号、実行情報、対象別ビルドとLeanの生出力。
- declaration-results.csv・item-results.csv・summary.json：解析結果。
- module-results.csv：準備ビルド・Leanの終了コード一覧。Leanの終了コード1は名前解決等の診断を含むことを表し、runnerの中断とは区別する。
- extra-axioms.csv・model-category-flags.csv：追加公理・ModelCategory文字列を含む型の一覧。

再解析：python3 -B research/kerodon-coverage/review/check/check_declarations.py parse --run-dir runs/all-20261107-01

再解析の終了コード1は未解決・名前解決失敗等があるという監査結果で、全件の実行は完了している。
数学的な対応を確認済みなのは、別途コミット済みのCh1全180項目。Ch2以降の段2・段3は未完了。
'''
(BASE / 'stage1-all-report.md').write_text(text)
print('validated', len(modules), 'modules;', len(refs), 'unique references;', len(items), 'items')
print('Lean return codes', dict(collections.Counter(m['lean_returncode'] for m in modules)))
