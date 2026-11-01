> **最新の状態：既存の生成補題の対応付け制約で停止。改訂版 §7-1 は未完了。詳細は [停止報告](w1-generated-declaration-stop.md)。以下は前回までの記録。**

# IF-W0-3 §10 再検収作業の途中停止

2026-10-29。作業ブランチ `infra/if-w0-3`。`git merge --ff-only main` は成功し、基準は `b1158d8004cd08c2797cddd0ab61799adc71a549`（指示追記 `0e0379c01` を含む）。
**改訂版 §7-1 には到達していない。w1.json は前回の27件のままであり、今回の処置の確定結果ではない。**

## 停止理由

UniverseHomotopy は全2宣言を Core.UniverseHomotopy へ切り出す指定となる。元の側が宣言0件になるため、既存の decl_snapshot.lean の空集合拒否にかかった。基準ビルド・分割直後のビルド・最小化候補のビルドは成功し、snapshot の取得で止まった。
```text
uncaught exception: snapshot selected no declarations
```
失敗した内側のコマンド（終了コード1）：
```sh
lake env lean --run scripts/refactor/decl_snapshot.lean \
  --modules SerrePositivity.InfinityCategories.DoldKanComparison.UniverseHomotopy \
  --output .lake/verify/prune-yg952rw2/4-snapshot.json
```
外側の試験（終了コード1）：
```sh
python3 -B scripts/refactor/test_targets_split_evidence.py universe
```
分割呼び出し：
```sh
python3 -B scripts/refactor/split_module.py \
  SerrePositivity.InfinityCategories.DoldKanComparison.UniverseHomotopy \
  SerrePositivity.InfinityCategories.Core.UniverseHomotopy \
  --moved SerrePositivity.InfinityCategories.DoldKanComparison.uliftHomotopy \
          SerrePositivity.InfinityCategories.DoldKanComparison.ulift_homotopyEquivalence \
  --snapshot .lake/verify/ifw0-3-revision/splits/universe/before.json \
  --output .lake/verify/ifw0-3-revision/splits/universe/plan.json \
  --apply --prune-imports
```

IF-W0-1 §0 の「既存のコード・監査・ビルドが想定外に失敗したとき」「直すには所有範囲の外を変える必要があるとき」に従い停止。decl_snapshot.lean と prune_imports.py は §10 の追加所有範囲に含まれない。両方とも変更していない。
修正案は、分割によって空になる側だけを明示的に扱い、両側を合わせた snapshot と全宣言の保存比較を必須にすること。一般の空 snapshot の拒否を無条件に外す案は採らない。実装は未着手。

## 復元・証拠

- 試験の全ソース変更をバイト列で復元確認。新しい Core.UniverseHomotopy.lean とそのビルド生成物を削除。
- prune 内の復元ビルド：終了0、8.700秒。外側の復元ビルド：終了0、5.394秒。
- `.lean` の git 差分なし。未コミット。
- `.lake/verify/ifw0-3-revision/splits/universe/results.json`：試験全体の結果・コマンド・所要時間。
- `.lake/verify/prune-yg952rw2/4-candidate-snapshot.log`：エラーの原文。
- `.lake/verify/prune-yg952rw2/results.json`：内側のビルド・最小化・復元記録。
- 下流全体の分割後ビルド・保存比較には未到達。imports を確定する証拠は未完成。

| 試験の段 | 終了コード | 秒 |
| --- | ---: | ---: |
| baseline-build | 0 | 9.138 |
| before | 0 | 49.788 |
| dry-run | 0 | 31.474 |
| apply-prune | 1 | 104.799 |
| restore-build | 0 | 5.394 |

## 完了した準備と単体試験

- validator に任意の imports フィールドを追加。両側のキー・配列・名前・重複・自己参照・存在しないプロジェクトモジュール・循環・snapshot の依存方向を検査する。実際の証拠の確認は別途必須と文書化。
- validator の結果に before/after の entry_edges を追加。
- targets_builder に --plans、--future-plans、--remove-edges、--add-edges、--snapshot を追加。後続窓の条件付き結果と現在の結果を分離する。
- test_targets_imports.py：16試験 PASS（終了0）。test_targets_builder.py：19試験 PASS（終了0）。既存 test_refactor_tools.py：11試験 PASS（終了0）。
- R66 の Join 系の下書き先を Core に変更。まだ w1.json の再生成・検査はしていない。

## 三案の計測途中結果

全ての入口とその直接・推移的利用元は `.lake/verify/ifw0-3-revision/analysis.json` に保存。以下は22候補ごとの要約であり、三案の最終選択表ではない。
下ろす集合は v 自身を含み、前回の27 move と承認された Join 3 move を仮定して、移し先より上の層を追加する。外部の汚染モジュール数はその閉包中の DG・KST・モデル圏を数えたもの。
入口は集計時点で対象を直接読む中核全体から採っているため、F2内部など同層の順方向利用者も含む。最終の「禁止入口の辺ごと」の表への絞り込み・三案選択は未完。
| 前回番号 | 対象末尾 | (a) S(v) 本数 | DG/KST/モデル圏の依存数 | (b) 中核利用元なしの入口数 / 全入口数 | (c) 分割証拠 |
| ---: | --- | ---: | ---: | ---: | --- |
| 1 | JoinSimplexFaces | 1 | 0 | 0 / 1 | 未確定 |
| 2 | JoinSimplexInclusions | 1 | 0 | 0 / 1 | 未確定 |
| 3 | JoinVertexSurjectivity | 1 | 0 | 0 / 2 | 未確定 |
| 4 | FilteredSpaceBridgeInput | 473 | 187 | 0 / 3 | 未確定 |
| 5 | FunctorIsoConstantEdges | 2 | 0 | 0 / 2 | 未確定 |
| 6 | PinchedSliceCompositionRealization | 11 | 0 | 0 / 2 | 未確定 |
| 7 | RightFibrationTerminalRepresentation | 943 | 672 | 0 / 2 | 未確定 |
| 8 | RoofTargetFunctor | 942 | 672 | 0 / 1 | 未確定 |
| 9 | SliceEvaluationPinched | 954 | 672 | 0 / 1 | 未確定 |
| 10 | UniverseHomotopy | 495 | 10 | 0 / 2 | 2宣言：snapshot失敗、復元済み |
| 11 | CoreIsofibration | 22 | 12 | 0 / 6 | 未確定 |
| 12 | CorePullbackIso | 17 | 12 | 0 / 4 | 未確定 |
| 13 | CoreTrivialFibration | 19 | 12 | 0 / 2 | 2宣言案：未実施 |
| 14 | FunctorIsoTransport | 2 | 0 | 1 / 41 | 未確定 |
| 15 | FunctorIsoTransportAlgebra | 64 | 12 | 0 / 21 | 未確定 |
| 16 | FunctorIsoWhiskerComposition | 2 | 0 | 0 / 25 | 未確定 |
| 17 | FunctorIsoChainTransport | 65 | 12 | 0 / 11 | 未確定 |
| 18 | FunctorIsoWhiskerCancellation | 84 | 12 | 0 / 25 | 未確定 |
| 19 | FunctorPointwiseColimitCriterion | 37 | 0 | 0 / 10 | 未確定 |
| 20 | IsoEndpointNormalization | 3 | 0 | 0 / 5 | 未確定 |
| 21 | SpaceLimitShapes | 122 | 81 | 0 / 4 | 2宣言案：未実施 |
| 22 | EnrichedFunctorCollageNerve | 272 | 78 | 0 / 1 | 未確定 |

## 確認済みの判断材料

- HL でコメントを除いた本文に ModelCategory を含むものは42本。QuillenCfCollage はその集合に入り、EnrichedFunctorCollageNerve の入口である。推移的中核利用元は同じ Quillen 系の30本と HL 集約。#22 を W2a に回す根拠となる。集約の扱いも後続窓で必要。
- UniverseHomotopy の入口は HL.ReflectedRepresentableComparison と HL.UniverseHomotopyReflection。どちらも Quillen 系42本には入らないため、#10 は W1 の分割対象。
- roof 系：Stable.SliceEvaluationNaturality は中核推移利用元55本、LoopCospanRepresentation は52本、TerminalRightFibrationComparison は54本。そのまま上げる条件は満たさない。
- R61a組1の判断は承認内容どおり F1/Universe/PinchedHom を残す。前回の読解記録にある逆向きの提案は撤回対象。本文の改訂と symbols 対応表の反転は停止により未反映。
- #4 は W2b へ送る判断を確認済み。W2b JSON はまだ作っていない。

## 未完了

CoreTrivialFibration と SpaceLimitShapes の分割証拠、入口ごとの三案の最終比較、w1.json/w1.md の改訂、改訂 JSON の validator、手作業を含めた W1 の終了条件判定は未完了。前回の数値を改訂後の結果として扱わない。
