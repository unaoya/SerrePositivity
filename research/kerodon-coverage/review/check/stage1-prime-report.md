# Kerodon 段1′の結果

全2,108種類の宣言記載のうち、段1で型と公理を確認できた394件を保持し、残る1,714件の名前を再検査した。
1,577件を一意に補正し、段2で参照できる記載は394件から1,971件になった。
手動確認に回す137件の内訳は、複数候補が通った71件、候補を生成できなかった64件、候補はあったが一つも通らなかった2件。

| 段1の判定 | 件数 | 段1′で保持 `found` | 一意補正 `renamed` | 複数候補 `ambiguous` | 候補なし・成功なし `manual` |
| --- | ---: | ---: | ---: | ---: | ---: |
| `found` | 394 | 394 | 0 | 0 | 0 |
| `not_found` | 1,602 | 0 | 1,530 | 70 | 2 |
| `unresolved_reference` | 111 | 0 | 46 | 1 | 64 |
| `check_failed` | 1 | 0 | 1 | 0 | 0 |
| 合計 | 2,108 | 394 | 1,577 | 71 | 66 |

集計単位は原記載のID。複数のKerodon項目で同じ記載が使われる場合は一度だけ数える。
段1の `not_found` は引用元モジュールを読み込んだ際に原記載の名前を解決できなかったという判定。
名前と型を確認した1,971件についても、Kerodonの主張との一致は段2で確認する。

## 補正規則

1. 引用元ファイルを開き、引用行で有効な `namespace`、`section`、`open` と `open … in` を追う。文書中のパス略記 `IC/` と `HomotopicalAlgebra/` は規定のパスに展開する。
2. 原記載の名前に加え、引用行の名前空間と `open` を補った候補を作る。前後12行以内に同じ末尾名の宣言があれば最寄りの宣言も参照し、原記載と一致する最長の修飾接尾名を優先する。説明文、匿名インスタンス、複数名の略記、近傍のprivate宣言は手動確認に回す。
3. 引用元モジュールだけを `import` して各候補に `#check` と `#print axioms` を実行する。全候補の検査が終わり、型と公理を確認できた候補が一つのときだけ `renamed` にする。成功が複数なら `ambiguous`、ゼロまたは候補なしなら `manual` とする。

たとえば `PiZeroConstant.homEquiv` は `SerrePositivity.SimplicialModel.PiZeroConstant.homEquiv` に、
段1で `check_failed` だった `Functor.const` は `CategoryTheory.Functor.const` に補正した。
スコープ解析の対応範囲と再実行手順は [段1′の実施方法](stage1-prime-method.md) を参照。

## 実行と照合

`446e88527` の実装で1,013モジュールを検査し、重複を除いた候補41,048件の出力を集計した。
型と公理を確認できた候補は1,683件、未知名は39,362件、フィールド記法のエラーは3件。
ビルド失敗・未実行モジュール・判定保留の記載はすべて0件。
元の記載ID、候補の検査件数、Leanの生出力と集計の対応、入力・ソース・スクリプトのハッシュを照合した。

成功候補1,683件と段2に渡す1,971記載について、標準3公理（`propext`、`Classical.choice`、`Quot.sound`）以外の公理と `sorryAx` は0件。
`#check` の型に `ModelCategory` が現れる成功候補は14件で、14件とも補正に採用した。
うち `SerrePositivity.SimplicialModel.simplicial_anodyne_eq_trivialCofibrations` の1件は `[ModelCategory SSet]` を要求し、他の13件は一般の圏にモデル圏構造を仮定する。
型に現れるこれらの仮定は段2で照合する。

- [resolution-results.csv](runs/stage1-prime-01/resolution-results.csv) に各原記載の判定、採用した引用、成功候補を記録。
- [verified-candidates.csv](runs/stage1-prime-01/verified-candidates.csv) に成功候補の型と公理を記録。
- [summary.json](runs/stage1-prime-01/summary.json) と [manifest.json](runs/stage1-prime-01/manifest.json) に件数と実行条件を記録。

`plan.json`、全候補の中間CSV、モジュールごとの生出力はローカルのrunに保存した。
