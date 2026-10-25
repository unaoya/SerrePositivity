# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v3（2026-10-24）**：D2 レーンの正本。所有：`Derived/Gluing/`。完了後は D に吸収。
> foundations.md §2 の β4・§6 の D2。dg 側は D の β5・β3、lax pullback は `F2/CatInfinity/` を読み取り専用で使う。
> 用途は K の Tamme・Land–Tamme の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-25）

### 現在地
- (a)〜(c) 完了。比較差は `gμ − νf`。実 Hom は同じ mapping cocone、全次数の単位・合成・微分を保持する。
- native dg 圏・左右射影・comma 比較、実円錐・全整数シフトと dg 自然な Yoneda 加群比較を構成済み。
  `dgGluing_isDGPretriangulated` は元 C・D の前三角性を明示入力とする。
- 因子 dg 準同値・順序 ⟨D,C⟩ の半直交性、H⁰ の実随伴・完全忠実な切断、K(Gluing) の実分解三角形を供給済み。
  元 H⁰ の未導入の三角構造や ∞ 随伴を結論していない。
- 一般対象宇宙の比較は対象・Hom を変えず、nerve の単体だけを共通宇宙へ ULift。二射影と augmentation の全 prism を保持する。
- (d) 完了。正本 `dgGluingLaxHomPullbackComparison` の実逆射・両往復ホモトピーを構成し、充満忠実性と既存の本質的全射性から比較同値を供給済み。
  元左右 Hom 鎖射影と augmentation 全族を保持し、任意の試験単体集合の関手 core から F2 の Kan 引き戻しへの実ホモトピー同値を供給済み。
- 正本比較は元の両 Hom 入力・augmentation 全族・二合成対応を保持する。二つの cube の共有面と標準合成三角形を貼り合わせ、相対二次元比較を選択済み二変形へ移す。
- D-13 の両単位則を同じ射影四面体の二単位面へ接続済み。左閉路は Λ³₂ の相対比較、右閉路は全正方形の厳密退化で零性を証明し、指定三辺の境界充填を無仮定で供給済み。
- (f) 導来 augmentation が可逆な元 gluing の充満 dg 部分圏を構成し、正本比較の通常 pullback への制限同値・安定性・実完全包含・元二射影との厳密整合を供給した。
- 同じ対象条件の実安定閉包との一致から、元の dg 包含と同じ cell 平坦商への `IsStableVerdierSequence` を供給。分解上の実小核・K-flat Hom・同じ商射影との屋根を保持する。
- D-16 は thick 閉包へ接続する方針に改訂。対象条件の共通宇宙の実ホモトピー圏での retract 閉性は証明済み。D-16 追加 (3) を適用し元対象条件と thick 閉包の一致を証明。実平坦 thick 核の本質像との一致・元包含への核反映・辺局所化から Sp の native `IsVerdierSequence` を供給済み。集約・公理監査も通過。
- D-15 の公開反映を適用し、対象条件と元 augmentation の `moduleQuasiIso` の同値を供給。Sp 正本への商の核一致は接続済み。追加 ULift 局所化の保存は公開供給待ちで、完成とはしていない。
- ④の Milnor 比較を Sp 正本の fiber 模型へ移し、元の自由対角の Hom 作用と厳密に照合。元二射影・零比較を保持し、その同じ一回 Perf 延長の Hom 準同型性・nerve 充満忠実性を証明。元小 Perf 対角と同じ cell 商の native Verdier 列は D-17 の生成判定・前三角性・完全性を明示して対象ビルド済み。

### G-1 d の三段目（固定）
- [x] ① 未追跡2ファイルの修正・個別検証・集約／監査への接続。
- [x] ② 正規化 prism を canonical 導来係数の実区間面へ照合。
- [x] ③ cube の入力固定変形と既存の選択変形を、二次元相対比較で接続。
- [x] ④ `dgGluingLaxHomDiagonalComparisonBoundary` の指定境界を保持して充填。
- [x] ⑤ 正本 `dgGluingLaxHomPullbackComparison` の実ホモトピー逆と往復則を構成。
- [x] ⑥ 充満忠実性・既存の本質的全射性から比較同値と全試験関手の ∞ 普遍性を供給。

### G-1 e の三段目（固定）
- [x] ① 共通宇宙の dg nerve の安定性・dg 関手の完全性を接続。
- [x] ② gluing の安定性と元の左右射影の完全性を供給。
- [x] ③ F2 の安定 lax pullback と正本比較の完全性を照合。
- [x] ④ 既存の半直交分解・K-8b の分裂との整合を接続。
- [x] ⑤ 集約ビルド・公理監査・引き継ぎの保存。

### G-1 f の三段目（固定）
- [x] ① 通常 pullback を表す元 dg gluing 内の充満部分圏と正本比較の制限を構成。
- [x] ② 通常 pullback の同値・安定性・実完全包含と二射影の整合を供給。
- [x] ③ D-9 の同じ平坦屋根・実小核・Verdier 商を gluing へ接続。
- [ ] ④ ⊙ の dg 同定と元の二射を保持する K-8 d8 の IsVerdierSequence を供給。
- [ ] ⑤ 集約ビルド・公理監査・D 向け引き継ぎを保存して停止。

### 残り（依存順）
1. (d) ①〜⑥完了。Tamme Remark 6 に対応する正本比較同値と全試験関手の普遍性を供給済み。
2. (e) 完了。元 C・D の前三角性から安定性・実完全射影・F2 の安定 lax pullback・両因子の本質像・K-8b の分裂を供給。Tamme Lemma 8。
3. (f) 通常 pullback と Verdier 商 ⊙ の dg 同定、K-8 d8 の `IsVerdierSequence` の供給。D-9 と共同。
   Tamme §1、Drinfeld Thm 3.4、β3 の平坦商。見積り 2〜3 日。完了時に D 向けの引き継ぎを整えて停止する。

### 主要宣言（型は Lean が正本）
- `DGGluingObject`・`dgGluingDifference`・`dgGluingHomComplex`・`dgGluingDGCategory`・`dgGluingToComma`
- `dgGluing_isDGPretriangulated`・`dgGluingFactors_semiorthogonal`・`dgGluingDecompositionTriangle_distinguished`
- `dgGluingUniverseDerivedNerveLaxComparison`・`dgGluingUniverseDerivedNerveLaxComparison_isEssentiallySurjective`
- `dgGluingUniverseDerivedNerveLaxComparison_isFullyFaithful`・`dgGluingLaxHomPullbackComparison_equivalence`・`dgGluingLaxHomPullbackComparisonInverse` と `_unit`／`_counit`
- `dgGluingUniverseDerivedNerveLaxEquivalence`・`dgGluingLaxFunctorEquivalence`・`dgGluingLaxFunctorCoreComparison_equivalence` と `_arrow`／`_inputs`
- `dgGluingHomDerivedCompositionInputPathComparison_equivalence`・`dgGluingLaxHomInputStrictComparison`
- `dgGluingNativeDerivedPreNormalizeCube`・`dgGluingNativeDerivedPostNormalizeCube`・`dgGluingNativeDerivedNormalizationCube_shared_face`
- `dgGluingNativeNormalizationFirstTriangle_eq`・`dgGluingNativeNormalizationLastTriangle_eq`
- `dgGluingCoefficientYonedaSpaceIso_inv_chainMap`・`dgGluingNativeCoefficientDomainIso_inv`
- `dgGluingNativeNormalizedPrism_canonical_coefficient`・`dgGluingNativeDerivedPostNormalizeCube_canonical_interval_face`
- `dgGluingNativeDerivedNormalizedIntervalPrism_normalization_exists`
- `dgGluingLaxHomFirstInputHomotopy_relative_comparison`・`dgGluingLaxHomLastInputHomotopy_relative_comparison`
- `dgGluingNativePreNormalizeTriangleFamily`・`dgGluingNativePostNormalizeTriangleFamily`
- `dgGluingNativeNormalizationPasting`・`DGGluingNormalizationProjectionInput`
- `dgGluingNormalizationCompositionTetrahedron`・`dgGluingNativeNormalizationAugmentationTetrahedron`
- `dgGluingNormalizationAugmentationTetrahedronHomotopy`・`dgGluingInputHomotopy_post_homMk_eq`
- `dgGluingHomotopyTriangleFilling_iff`・`dgGluingHomotopyTriangleFilling_transfer`
- `dgGluingLaxHomDiagonalComparisonBoundary_filling_of_input_triangle`
- `dgGluingLaxHomDiagonalComparisonBoundary`・`dgGluingLaxHomFirstInputHomotopy_over`・`dgGluingLaxHomLastInputHomotopy_over`

### 依存と提供
- 読み取り専用：`Derived/` の β5・β3、`F2/CatInfinity/`、`Core/`・`F1/`・`F1B/`。
- 提供先：Sp（K-8 の ⊙）、K-B・K-S•（具体的 Verdier 列）。D2 の f 完了後は D が Gluing を吸収。
- β5 の入口：`dgAlgebraDerivedInfinityCategory`、`Bimodule`、`Morita.kernelTensor`、`dgKernelDerivedInfinity`。
- D の Small 不要 Direct prism 自然性は `059a227ad`。coherent prism 自身の自然性は追加供給 `9b40d1218`。
  入口は `DGPinchedCompositionClosedFamilyNaturality` の `dgPinchedCompositionFamilyPrism_closed_first_naturality`／`closed_second_naturality`。
- `dgGluingNormalizationProjectionInput_naturality` で六等式を無仮定で実例化済み。全標準面と固定標的輸送を保持する。
  標準面の恒等入力射影・前後終側の replacement 全三角形の一致は照合済み。厳密両単位則は D-13 で供給済み。両単位は主経路へ接続済み。F1B の公開 `RelativeDiagramHomotopy` を直接利用し、Λ³₂ を固定した相対四面体比較の存在は実例化済み。

### 設計上の確認点・次の一手
- 前 cube の正規化端は `dgGluingIdentityCommaObject` を始対象とする。第一三角形の固定辺は元 augmentation から恒等辺へ変わる。
  したがって、全時間の第一三角形族をそのまま元の始辺固定入力 fiber 内のホモトピーとは扱えない。
- **採用（2026-10-24、コーディネータ指示）**：共有面と側面の標準合成三角形も含む貼り合わせを先に構成し、その相対二次元比較を選択済み二変形へ移す。
  二つの cube それぞれの三角形族を直接、元の固定辺を保つ入力 fiber へ入れる前提を置かない。
  隔離していた射影自然性（前後・終側の三角形それぞれ二射影、計六等式）は、追加供給により実例化済み。
  公開界面と三段目③〜⑥の順序は不変。三段目の完了では停止しない。
- **次工程 (f)**：③の本質像輸送・native Verdier 列は集約・監査済み。④は D-17 の生成判定を明示入力に隔離し、元小 Perf 対角と cell 平坦商の Verdier 条件を組み立て、固定 ν の射影の付け替えへ引き継ぐ。D-17・D-18 と追加 ULift 局所化の公開供給が届けば代入する。
- **採用（2026-10-25、コーディネータ指示）**：④では `dgGluingMilnorSquareComparison` が準同型である dg 形の Milnor 条件だけを四角形の仮定に取る。Sp 正本の `HomotopyPullbackModel.algebra` と同じ比較射を使い、元対角の充満忠実性と元二射の `IsVerdierSequence` を導く。商は `resolvedDGQuotientFunctor` に固定し、未分解 path 商との比較・対角像の `localKFlat` は第 I 段で要求しない。K-S• が再開時に元射影を付け替える。具体例の検証は K-S• の再開後。
  公開界面・採用済み貼り合わせ経路・③〜⑥の順序は不変。
- 正本は `dgGluingLaxHomPullbackComparison`。元の両 Hom 入力・augmentation prism・二三角形を保持する。
  個別の入力固定ホモトピーだけから全 path 比較の一致を結論しない。主経路へ新しい仮定を追加しない。

### 未コミット・既知の問題
- (e) 完了。`UniverseDerivedExactness` は D-14 の ULift 保存・混在宇宙完全性と既存 tensor 比較から、元の Yoneda・係数脚・実分解の完全性を供給する。二脚完全性の隔離は解消済み。
- `CanonicalStableStructure` は元 C・D の前三角性だけから F2 安定性・元二射影による実 cofiber 判定・native 半直交分解・元二射影の値を持つ Tamme 積同値を供給する。
- `NativeCFactorKernel` は Sp の公開 `LaxSecondProjectionKernel.snd_kernel`（`32ed8091f`）を利用する。C・D 両因子の元の H⁰ 零性条件は、canonical native 半直交分解の二包含の本質像に一致する。実随伴・充満忠実性・交差写像空間の可縮性・対応する分裂 Verdier 列も供給済み。
- ④検証済み：`MilnorSmallPerfectFaithfulness`・`MilnorDiagonalStableImage`・`MilnorDiagonalThickImage`・`MilnorResolvedQuotient`・`MilnorFlatThickTransport`・`MilnorResolvedKernel`・`MilnorResolvedVerdier` は集約13142 jobs・監査948モジュール8815宣言を通過。D-17 は `DGGluingMilnorSmallPerfectGeneration` に隔離。D-18 補足の順方向輸送は供給待ち。K-S• は `dgGluingMilnorResolvedProjection` へ射影を付け替え、`dgGluingMilnor_isResolvedVerdierSequence` を使う。③の集約は12744 jobs、監査は941モジュール・8772宣言を通過。吸収対象は元包含・同じ平坦屋根を保つ公開宣言。未追跡 `HomTargetCommaFunctor` は元終域 comma 比較を束ねる接続として対象ビルド中。
- d の検証済み：集約ビルド 8946 jobs、公理監査 896 モジュール・8303 宣言。許容三公理のみ。新規 sorry・axiom・主経路 ModelCategory 仮定なし。
  ログ：`/tmp/d2-v3-canonical-equivalence-universal-property-aggregate-build.log`・`/tmp/d2-v3-canonical-equivalence-universal-property-audit.log`。指定充填と入力付き path の実逆射・両往復変形を無条件で接続済み。同一対角・元二入力を持つ四座標比較まで同値性を移送済み。四座標の厳密同型と元矢印・左右鎖射影を回収する。
- 検証済み部分をコミットし、正本標的から元二入力と二合成対応を持つ区間座標への実同値を構成済み。元正本比較の矢印射影と左右 Hom 鎖射影を厳密に回収し、既存の四座標比較の両射影との一致を供給済み。底の二作用も同定し、正本の実逆射と比較同値・全試験関手 core の普遍性を無条件で接続済み。数学的未完は f。
- β5 の Bimodule は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`、比較差は `gμ − νf`。

## 規約
- 配置：`SerrePositivity/InfinityCategories/Derived/Gluing/`。集約：`Derived/Gluing.lean`。監査：`scripts/audit_derived_gluing.lean`。
- foundations.md §8 v3。所有ファイルのみ `set -o pipefail` のうえ `git commit --only`。他レーンは読み取り専用。
- 新規 sorry・公理・引用なし。主経路へ ModelCategory 仮定を入れず、heartbeat 上限は増やさない。移動・改名・削除は R の停止窓。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts、Drinfeld 2004。実施記録はコミットメッセージ。計画本文は300行以内。
