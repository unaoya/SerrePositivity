# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v5（2026-10-27）**：D2 分担完了・閉鎖。K-S• 向け全 lax／cone 比較の三入力を供給し、ユーザーによる確認・中継済み。所有：`Derived/Gluing/` と集約・監査。
> foundations.md §2 の β4・§6 の D2。dg 側は D の β5・β3、lax pullback は `F2/CatInfinity/` を読み取り専用で使う。
> 用途は K の Tamme・Land–Tamme の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-27、閉鎖）

### K-S• への最終供給
- ユーザーが `eaa2179b0` までの三入力を確認し、K-S• へ中継済み（2026-10-27）。D2 の今回分担は完了・閉鎖。消費側の実装は K-S• 所有であり、D2 の未完了作業として残さない。
- 名前空間は `SerrePositivity.InfinityCategories`。以下はいずれも引数 `R d` の実例で、消費側の型は変更していない。
- 元二脚：`dgGluingOriginalLaxComparisonInput : DGOdotMilnorOriginalLaxComparisonInput R d`（`OriginalInputLaxEquivalence`、`ca32426eb`）。指定左右入力同値の逆と両射影の全 `FunctorIso` を保持する。
- 恒等二脚：`dgGluingIdentityLaxComparisonInput : DGOdotMilnorIdentityLaxComparisonInput R d`（`IdentityLaxComparisonInput`、`88112f27c`）。gluing・difference・diagonal・cone の全4欄を実例化。対角欄は `dgGluingIdentityInputDiagonalIso`、cone 欄は `dgGluingIdentityInputConeIso`。
- 元 corner cone：`dgGluingOriginalLaxConeComparisonInput : DGOdotMilnorOriginalLaxConeComparisonInput R d`（`OriginalInputConeComparison`、`eaa2179b0`）。第1入力に `dgGluingOriginalInputConeIso` を `.withCone` で接続し、指定 corner 評価と Yoneda 全比較を保持する。
- 集約 `SerrePositivity.InfinityCategories.Derived.Gluing` から三入力の型照合を実施済み。最終集約ビルドは13,414 jobs、公理監査は1,083モジュール・11,504宣言で通過。新規 sorry・公理・ModelCategory 仮定・heartbeat 上限増加なし。

### 一般 API と採用経路
- 元終域向け Hom 比較を D2 内で直接構成した。F2 への供給依頼は行っていない。S 構成固有の固定入力への接続は結論のアダプタに置く。
- `dgGluingHomTargetLaxHomPullbackComparisonInverse`・`_unit`・`_counit` は元 lax Hom 標的自身の実逆と両往復則。入力付き path 模型だけの逆と区別する。
- `dgGluingHomTargetNerveLaxEquivalence` と `dgGluingHomTargetDerivedLaxEquivalence`・`_fst`・`_snd` は元二脚の全比較。恒等特殊化は `dgGluingIdentityHomTargetLaxEquivalence`。
- `dgGluingIdentityNativeDiagonalIso` は元対角の全比較。`dgGluingIdentityNativeConeComparison` は実右軸上の Yoneda 全比較・対角の指定収縮・完全性を局所化判定へ代入した恒等全 cone 比較。
- `dgGluingHomTargetToIdentity` は元左右 Hom と第三 primitive を全次数で保持する dg 関手。`_left`・`_right`・`_comma`、augmentation 全族の `_prism`・`_homotopy`・`_arrow`、元実 cone の `_cone` は厳密に整合する。
- `dgGluingHomTargetNativeConeComparison` は一般の元共通終域で元 lax 比較後の選択 cofiber 差と元実 Perf cone 関手を全比較する。`laxCospanIsoCofiberComparison` により同じ指定 cospan 全比較のまま固定 ν へ輸送した。
- `zeroSourceModuleConeIso`・`dgGluingIdentityRightAxisPerfectConeIso` は実零対象と元 cone 包含を使う。`dgPerfectValuedFunctor_isExactFunctor` は小全像包絡を通じて完全性を示し、全 Perf の Small 性を要求しない。
- **R 候補（D2 の残作業ではない）**：`F2.laxPullbackCospanIsoEquivalence` と関連する新規 F2 10葉の F2 集約登録。現状の登録はユーザー指示どおり D2 集約・監査のみ。移動・改名・削除は R の停止窓へ委ねる。

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
- (f) ④の Milnor 比較を Sp 正本の fiber 模型へ移し、元小 Perf 対角の実自由 End と厳密に照合。D-17 の生成判定・D-18 の前三角性・D-19 の代表合成整合を適用し、Milnor 条件だけから元対角の全 Hom 準同型性・充満忠実性と同じ cell 商の native Verdier 列を供給。生成判定の明示仮定は解消済み。

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
- [x] ④ ⊙ の dg 同定と元の二射を保持する K-8 d8 の IsVerdierSequence を供給。
- [x] ⑤ 集約ビルド・公理監査・D 向け引き継ぎを保存して停止。

### D への移管範囲
1. (d) ①〜⑥完了。Tamme Remark 6 に対応する正本比較同値と全試験関手の普遍性を供給済み。
2. (e) 完了。元 C・D の前三角性から安定性・実完全射影・F2 の安定 lax pullback・両因子の本質像・K-8b の分裂を供給。Tamme Lemma 8。
3. (f) ①〜⑤完了。通常 pullback と同じ cell 平坦商の dg 同定、および Milnor 条件下の元小 Perf 対角の Verdier 列を供給。G-1 は完了。2026-10-26 に K-S• 全比較の工程を追加して D2 を再開。

### 主要宣言（型は Lean が正本）
- `DGGluingObject`・`dgGluingHomComplex`・`dgGluingToComma`・`dgGluing_isDGPretriangulated`
- `dgGluingFactors_semiorthogonal`・`dgGluingDecompositionTriangle_distinguished`
- `dgGluingLaxHomPullbackComparison_equivalence`・`dgGluingLaxHomPullbackComparisonInverse` と `_unit`／`_counit`
- `dgGluingUniverseDerivedNerveLaxEquivalence`・`dgGluingLaxFunctorCoreComparison_equivalence` と `_arrow`／`_inputs`
- `dgGluingPullbackProperty_iff_quasiIso`・`dgGluingPullbackProperty_thickClosure_iff`
- `dgGluingPullback_thickEssentialImage_iff`・`dgGluingPullbackFlatQuotient_zero_iff`・`dgGluingPullbackFlatQuotient_isLocalization`
- `dgGluingPullback_isNativeVerdierSequence`（元の通常 pullback 包含、同じ cell 平坦商）
- `dgGluingMilnorSquareComparison`・`DGGluingMilnorSquare`・`dgGluingMilnorAlgebraDiagonal_homQuasiIso`
- `dgGluingMilnorResolvedProjection`・`dgGluingMilnor_isResolvedVerdierSequence_of_milnor`（元小 Perf 対角）
- `dgGluingMilnorSmallPerfectDiagonal_homQuasiIso_of_milnor`・`dgGluingMilnorDiagonalExactMap_isFullyFaithful_of_milnor`
- `dgGluingMilnorSourceGenerator_generates`・`dgGluingMilnorSmallPerfectDiagonal_homQuasiIso_of_generator`

### 依存と提供
- 読み取り専用：`Derived/` の β5・β3、`F2/CatInfinity/`、`Core/`・`F1/`・`F1B/`。
- 提供先：Sp（K-8 の ⊙）、K-B・K-S•（具体的 Verdier 列）。D2 の f 完了後は D が Gluing を吸収。
- β5 の入口：`dgAlgebraDerivedInfinityCategory`、`Bimodule`、`Morita.kernelTensor`、`dgKernelDerivedInfinity`。
- D の Small 不要 Direct prism 自然性は `059a227ad`。coherent prism 自身の自然性は追加供給 `9b40d1218`。
  入口は `DGPinchedCompositionClosedFamilyNaturality` の `dgPinchedCompositionFamilyPrism_closed_first_naturality`／`closed_second_naturality`。
- `dgGluingNormalizationProjectionInput_naturality` で六等式を無仮定で実例化済み。全標準面と固定標的輸送を保持する。
  標準面の恒等入力射影・前後終側の replacement 全三角形の一致は照合済み。厳密両単位則は D-13 で供給済み。両単位は主経路へ接続済み。F1B の公開 `RelativeDiagramHomotopy` を直接利用し、Λ³₂ を固定した相対四面体比較の存在は実例化済み。

### D 向けの接続手順・設計上の確認点
- 前 cube の正規化端は `dgGluingIdentityCommaObject` を始対象とする。第一三角形の固定辺は元 augmentation から恒等辺へ変わる。
  したがって、全時間の第一三角形族をそのまま元の始辺固定入力 fiber 内のホモトピーとは扱えない。
- **採用（2026-10-24、コーディネータ指示）**：共有面と側面の標準合成三角形も含む貼り合わせを先に構成し、その相対二次元比較を選択済み二変形へ移す。
  二つの cube それぞれの三角形族を直接、元の固定辺を保つ入力 fiber へ入れる前提を置かない。
  隔離していた射影自然性（前後・終側の三角形それぞれ二射影、計六等式）は、追加供給により実例化済み。
  公開界面と三段目③〜⑥の順序は不変。三段目の完了では停止しない。
- **K-S• の再開時**：`MilnorVerdierSequence` を import し、`DGGluingMilnorSquare R d` を検証する。元の小 Perf 対角は保持し、元射影を `dgGluingMilnorResolvedProjection R d` へ付け替え、`dgGluingMilnor_isResolvedVerdierSequence_of_milnor R d h` を適用する。旧 `_of_generation` の生成入力は不要。
- `MilnorFreeDifferenceSquare` は元自由 End と同じ Milnor fiber の比較差の正方形を供給する。`MilnorFreeDiagonalComparison` は元二射影・零比較を保持する対角作用の等式を供給する。

- **採用（2026-10-25、コーディネータ指示）**：④では `dgGluingMilnorSquareComparison` が準同型である dg 形の Milnor 条件だけを四角形の仮定に取る。Sp 正本の `HomotopyPullbackModel.algebra` と同じ比較射を使い、元対角の充満忠実性と元二射の `IsVerdierSequence` を導く。商は `resolvedDGQuotientFunctor` に固定し、未分解 path 商との比較・対角像の `localKFlat` は第 I 段で要求しない。K-S• が再開時に元射影を付け替える。具体例の検証は K-S• の再開後。
  公開界面・採用済み貼り合わせ経路・③〜⑥の順序は不変。
- 正本は `dgGluingLaxHomPullbackComparison`。元の両 Hom 入力・augmentation prism・二三角形を保持する。
  個別の入力固定ホモトピーだけから全 path 比較の一致を結論しない。主経路へ新しい仮定を追加しない。

### 供給済み範囲と移管上の注意
- G-1 と K-S• 向け三入力供給は集約・公理監査済み。公開名はユーザー経由で報告・中継済み。以下の強化・消費側作業は今回の D2 閉鎖を妨げる残件ではない。
- native の通常 pullback 包含と同じ cell 平坦商の Verdier 列は完成。任意の追加 ULift における局所化保存は公開供給待ちであり、この強化を結論していない。
- 未分解 path 商 `dgQuotientNerve` と cell 平坦商の比較・対角像の `localKFlat` は第 I 段の要求外。元の `dgOdotQuotientInput.projection` をそのまま最終商射に使わない。
- Milnor 条件の具体例の検証と固定 ν の商射影の付け替えは K-S• の再開時に行う。
- `UniverseDerivedExactness` は D-14 の ULift 保存・混在宇宙完全性と既存 tensor 比較を利用し、元 Yoneda・係数脚・実分解の完全性を供給する。
- `CanonicalStableStructure`・`NativeCFactorKernel` は元二射影と両因子の本質像を保持し、Tamme 積同値・native 半直交分解・分裂 Verdier 列を供給する。
- β5 の Bimodule は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`、比較差は `gμ − νf`。

## 規約
- 配置：`SerrePositivity/InfinityCategories/Derived/Gluing/`。集約：`Derived/Gluing.lean`。監査：`scripts/audit_derived_gluing.lean`。
- foundations.md §8 v3。所有ファイルのみ `set -o pipefail` のうえ `git commit --only`。他レーンは読み取り専用。
- 新規 sorry・公理・引用なし。主経路へ ModelCategory 仮定を入れず、heartbeat 上限は増やさない。移動・改名・削除は R の停止窓。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts、Drinfeld 2004。実施記録はコミットメッセージ。計画本文は300行以内。
