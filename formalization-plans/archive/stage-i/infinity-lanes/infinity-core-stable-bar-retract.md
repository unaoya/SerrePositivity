# D：coherent bar の変形 retract（工程 A、完了）

## 現在地
- 工程 A の無条件の変形 retract を証明済み。専用 All は 3739 jobs、専用監査は65葉529宣言で成功（標準三公理のみ）。
- チャット稼働の基準は 2026-10-25 18:07 頃。24 時間の期限は10-26 18:07 頃（新割り当てでリセットしない）。
- 所有：Derived/CoherentBar/Retract/ の新規葉・All・専用監査。D-bar の既存 CoherentBar/ は読み取り専用のまま。
- 有限段階の実正規化作用素を普遍 P 係数と無条件に比較し、安定作用素の全退化列の零性を証明した。
- 同じ正規化実加群・同じ閉射影を使う修正包含は閉じており、包含≫射影は厳密に恒等、射影≫包含は既存の安定作用素そのもの。
- 恒等への比較は ModuleHomotopy。評価ごとの鎖ホモトピーだけに弱めず、全次数の dg 作用を保持する。

## D-bar への公開入口
- モジュール：`Derived.CoherentBar.Retract.DeformationRetract`（または `Retract.All`）。名前空間は `SerrePositivity.InfinityCategories`。
- 修正包含：`dgCoherentBarNormalizedModuleInclusionUnconditional`。
- 厳密な分裂：`dgCoherentBarNormalizedModuleInclusionUnconditional_projection`。
- 安定作用素との一致：`dgCoherentBarNormalizedModuleProjectionUnconditional_inclusion`。
- 全作用付き鎖ホモトピー：`dgCoherentBarNormalizedModuleRetractHomotopyUnconditional`。
- 一般の既存 MC 証明を保持する版：`dgCoherentBarNormalizedModuleInclusion`・`_projection`、`dgCoherentBarNormalizedModuleProjection_inclusion`、`dgCoherentBarNormalizedModuleRetractHomotopy`。
- 無条件版の仮定：R の CommRing、D の DGCategory と Small.{u}、I : SSet.{u}、F : ULift I ⟶ dgNerve R (RightModule R D)。MC・退化消去・係数比較の追加入力は不要。
- 元の bar・正規化模型・射影・安定自己写像・既存宣言は変更していない。移動・改名・削除なし。

## 証明の接続
1. [x] prefix と退化の全 Hom の合成比較、正位置の全 prefix 和の相殺、零位置の単位面の相殺。
2. [x] 始点保存作用の厳密合成と線形係数押出し、普遍 PInfty 係数の全退化列の消滅。
3. [x] Mathlib Hσ の全場合の面表示と普遍係数、始点支持、自然性、実境界との無条件比較。
4. [x] P_succ による有限段比較、安定作用素の退化消去、修正包含・分裂・ModuleHomotopy への無条件代入。
5. [x] 専用 All の終端後に専用監査を完了。限定コミットで公開する。

## 主要な内部入口
- `StageCoefficientComparison.dgCoherentBarStageCoefficientComparison`。
- `BoundaryCoefficientComparison.dgCoherentBarNormalizationBoundary_coefficients`。
- `DeformationRetract.dgCoherentBarNormalizationKillsDegenerate`。
- `CorrectedInclusion` の明示入力版は内部の一般降下として保持し、上記入口で無条件証明を代入する。

## 次工程
- ユーザーの追加割り当てに従い、D 本体は CoherentBar/Compact/ の c2・c6・c7 を担当する。
- 正本：`infinity-core-stable-bar-compact.md`。D-bar は native 余錐・普遍性・filtered 評価比較を担当する。
- c2 の仮定は全 native κ-filtered な coherent 図式の比較。D-e の公開型は中継待ちで、strict 比較や poset 制限で代用しない。

## 運用
- 新規 sorry・公理・引用なし。ModelCategory SSet 等の instance を主経路へ入れない。
- 新規葉のみ。既存の D-bar 模型と他レーンのファイルは読み取り専用。
- All の終端後に専用監査。根のビルド・.lake の削除はしない。
- set -o pipefail のうえ所有パスのみ git commit --only。実施記録はコミット本文。
