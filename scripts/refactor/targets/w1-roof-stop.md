> **最新の状態：既存の生成補題の対応付け制約で停止。改訂版 §7-1 は未完了。詳細は [停止報告](w1-generated-declaration-stop.md)。以下は前回までの記録。**

# IF-W0-3 §10.4：roof 系の宣言分析による停止報告

2026-10-29。worktree `SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3`。
`git merge --ff-only main` は成功。HEAD は `4ae08cfe0b9d544303fa301e78ddf232cffda7c4`。

**§10.4-4 の停止条件に該当した。改訂版 §7-1 は未完了。**
`SliceEvaluationNaturality` と `TerminalRightFibrationComparison` で
D_forb ∩ D_core が空でない。指定どおり、その先の移動・分割・JSON 改訂には進んでいない。

## 計測方法

- 3 本の既存モジュールを `lake build` してから、修正した `decl_snapshot.lean` で同時に取得。
- snapshot は12行。公開親宣言9件と `loopCospanConeRepresentation` の補助宣言3件。
- D_forb は、型・本体・定理の証明の中の定数が Derived のモジュールに属する公開親宣言。補助宣言は親にまとめた。この設定では Derived が最上位の層。
- D_core は、別の中核モジュールの本文に宣言名の参照がある公開親宣言。中核は `layers.json` の `core` に従い、コメント・文字列を除去し、識別子境界で検索した。同じファイル内の参照と宣言自身の定義行は数えない。
- 後述の交わりの参照は実際の証明内の使用を目視確認した。import や docstring に書かれただけのものではない。
- D_forb は定数の直接依存に基づく。import 閉包や、同一ファイル内の別宣言を介した推移依存の件数とは区別する。

| 入口ファイル（Stable 以下） | 公開親宣言 | D_forb | D_core | 交わり |
| --- | ---: | ---: | ---: | ---: |
| SliceEvaluationNaturality | 2 | 2 | 1 | 1 |
| LoopCospanRepresentation | 5 | 1 | 1 | 0 |
| TerminalRightFibrationComparison | 2 | 1 | 2 | 1 |

## 停止の根拠となる鎖

以下のパスは `SerrePositivity/InfinityCategories/` 以下。宣言の共通名前空間は `SerrePositivity.InfinityCategories`。

1. `Stable/TerminalRightFibrationComparison.lean:98` の証明
   → `Stable/SliceEvaluationNaturality.lean:45` の `roofSliceEvaluationHomotopy_postcomp_h`
   → `Derived/SliceEvaluationPinched.lean:19` の `roofSliceEvaluationHomotopy_precomp_h`。
   同じ宣言は `Derived/RoofTargetFunctor.lean:28` の `roofTargetSliceMap` と
   `Derived/SliceEvaluationHomotopy` の `roofSliceEvaluationHomotopy` も直接使う。
2. `Stable/TerminalComparisonFiberTransfer.lean:81` の証明
   → `Stable/TerminalRightFibrationComparison.lean:31` の `terminalComparisonIntervalFamily_isQCatEquivalence`
   → `Derived/RightFibrationTerminalRepresentation.lean:31` の `roofTargetSliceMap_trivialKanFibration`
   （実際の呼び出しは `TerminalRightFibrationComparison.lean:48`）。
   この宣言はほかにも Derived の `pinchedFamilySlice`・`roofTargetSliceMap`・
   `roofTargetSliceMap_projection`・`roofSliceEvaluationHomotopy`・
   `roofSliceEvaluationHomotopy_pinched_h` を使う。

これらの宣言だけを Derived へ上げても、中核の利用元から禁止側への辺が残る。
§10.4-4 は「交わるなら……鎖を報告して止める」と指定しているため停止する。

## 集合と参照箇所

### SliceEvaluationNaturality

- D_forb: `roofSliceEvaluationHomotopy_postcomp_h`, `roofTargetSliceMap_uncurry`
- D_core: `roofSliceEvaluationHomotopy_postcomp_h`
- intersection: `roofSliceEvaluationHomotopy_postcomp_h`

中核の外部参照：

- `roofSliceEvaluationHomotopy_postcomp_h` ← `SerrePositivity/InfinityCategories/Stable/TerminalRightFibrationComparison.lean:98`：`rw [roofSliceEvaluationHomotopy_postcomp_h, ← hb,`

### LoopCospanRepresentation

- D_forb: `loopCospan_coneRepresentation_exists`
- D_core: `loopSquare_pullbackCone_vertex`
- intersection: ∅

中核の外部参照：

- `loopSquare_pullbackCone_vertex` ← `SerrePositivity/InfinityCategories/Stable/LoopConeClassifierInterval.lean:39`：`rw [loopSquare_pullbackCone_vertex] at h`

### TerminalRightFibrationComparison

- D_forb: `terminalComparisonIntervalFamily_isQCatEquivalence`
- D_core: `intervalFamilyHomotopy_h_injective`, `terminalComparisonIntervalFamily_isQCatEquivalence`
- intersection: `terminalComparisonIntervalFamily_isQCatEquivalence`

中核の外部参照：

- `intervalFamilyHomotopy_h_injective` ← `SerrePositivity/InfinityCategories/Stable/LoopConeClassifierFiberEquivalence.lean:48`：`apply intervalFamilyHomotopy_h_injective`
- `intervalFamilyHomotopy_h_injective` ← `SerrePositivity/InfinityCategories/Stable/TerminalComparisonFiberTransfer.lean:68`：`apply intervalFamilyHomotopy_h_injective`
- `intervalFamilyHomotopy_h_injective` ← `SerrePositivity/InfinityCategories/Stable/TerminalComparisonFiberTransfer.lean:75`：`apply intervalFamilyHomotopy_h_injective`
- `terminalComparisonIntervalFamily_isQCatEquivalence` ← `SerrePositivity/InfinityCategories/Stable/TerminalComparisonFiberTransfer.lean:81`：`have hE := terminalComparisonIntervalFamily_isQCatEquivalence p t ht x HE`

## 修正と試験

- `decl_snapshot.lean`：0件の例外を撤去し、`count` を追加。0件でも空配列を書いて終了0。
- 同スクリプト：宣言ごとの `uses_modules` を追加。既存の `used_modules` は利用側との互換性のため残し、同じ値を出力。定理の証明の定数も含む。
- `compare_snapshots.py`：空集合の拒否を撤去。空同士は PASS、非空→空は removed、空→非空は added として FAIL。
- 新規 `test_snapshot_empty.py`：単体3件 PASS。実 Lean の空モジュールと証明依存の試験も PASS。
- 既存 `test_refactor_tools.py`：11件 PASS。`git diff --check`：PASS。

| 実行 | 結果 | 終了コード |
| --- | --- | ---: |
| roof 3本の `lake build` | 成功、6152 jobs（既存の警告あり） | 0 |
| roof 3本の snapshot | count 12 | 0 |
| 宣言0件の実 Lean fixture の build / snapshot | count 0、declarations [] | 各0 |
| 宣言1件の fixture の build / snapshot | count 1、証明の True.intro を検出 | 各0 |
| 空→空の compare CLI | PASS、changes [] | 0 |
| 空→1件の compare CLI | FAIL、added 1件 | 1（期待どおり） |
| 1件→空の compare CLI | FAIL、removed 1件 | 1（期待どおり） |

fixture の `.lean` とビルド生成物は finally で削除済み。
本体の Lean ソースは変更していない。`.lean` の差分は承認範囲内の `scripts/refactor/decl_snapshot.lean` だけ。

## 保存した証拠

- `.lake/verify/ifw0-3-roof/build.log`：既存3本のビルド。
- `.lake/verify/ifw0-3-roof/snapshot.json`：12行の構造・定数・定義元モジュール。
- `.lake/verify/ifw0-3-roof/analysis.json`：集合、全外部参照の行、Derived の定数名と定義位置。
- `.lake/verify/ifw0-3-roof/empty-tests/commands.json`：実 Lean と compare の実コマンド・終了コード。
- 同ディレクトリの `empty.json`・`one.json`・比較結果・各ログ。
- `.lake/verify/ifw0-3-roof/refactor-tests.log`・`empty-unit-tests.log`。

## 未完了と変更範囲

`w1.json` は前回の27 move のまま。今回の処置を反映した JSON としては使用しない。
UniverseHomotopy の move 用 imports 対応・その場での prune 証拠、残る分割証拠、
三案の最終比較表、改訂 JSON の validator、手作業込みの W1 判定は未完了。
今回の交わりの判明後にこれらの作業へは進んでいない。コミットなし。

今回変更した実装・試験は `decl_snapshot.lean`、`compare_snapshots.py`、`test_snapshot_empty.py`。
今回の文書変更は本報告と、`w1.md`・`w1-revision-stop.md`・R61b archive の最新停止先への案内。
前回からの validator・targets_builder・対象 JSON 等の未コミット差分は維持している。
