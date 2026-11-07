# 段1・全件検査の完了報告（2026-11-07 JST）

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
| unresolved_reference | 111 |
| found | 394 |
| not_found | 1602 |
| check_failed | 1 |

foundは型と公理の両方を確認したもの。not_foundは指定されたimportで原記載の名前が解決しなかったもの。
**数学的な内容が存在しないという判定ではない。** 名前空間の不足、移動後の名前のずれ、記法・射影の扱いなどを段2で解決する必要がある。
例えばPiZeroConstant.homEquivはSerrePositivity.SimplicialModel.PiZeroConstant.homEquiv、
SimplicialObjectはCategoryTheory.SimplicialObjectが正しい。Ch1では補正後の別runで実在を確認した。
本集計はitems.csvを変更せず原記載を検査した集計であり、Ch1の補正結果を混ぜていない。

check_failedの1件はFunctor.const。修飾が不足しており、別のconstへのフィールド記法として解釈されるエラーになった。
CategoryTheory.Functor.constへの補正後の成功はCh1の証拠に保存済み。

## 公理と型の仮定

found 394件で標準3公理（propext、Classical.choice、Quot.sound）以外は0件。sorryAxの検出も0件。
取得できた型のModelCategory文字列による抽出は0件。該当一覧はmodel-category-flags.csv。
名前解決できなかった宣言と未解決記載について、公理や仮定の健全性を承認したという意味ではない。
この段は各主張の仮定が数学的に妥当かを精査する段2とは別であり、ModelCategory以外の強すぎる型クラス仮定も段2で確認する。

## 項目単位の集計

- needs_review: 1371
- found: 301
- no_declarations: 1881

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
