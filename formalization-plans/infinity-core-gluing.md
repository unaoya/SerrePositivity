# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §2 の β4、§6 の D2。D レーンの β5（D(A)、双加群、相対 tensor・Hom）と
> F1b の F2L-2〜4（Cat_∞ の lax pullback、安定性）を読み取り専用で使い、dg gluing の dg nerve が lax pullback であることを証明する。
> 用途は K-基盤 2（Tamme・Land–Tamme）の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-22）

### 現在地
- 工程 (a) 完了。`DGGluingObject` の対象、比較差 `gμ − νf` の mapping cocone としての実 Hom 複体、全次数の微分・単位・合成・結合律を構成。
  native dg 圏、左右 dg 射影、実 comma・通常 kernel comma への比較関手を供給。native/kernel Hom 同型は全次数の合成・単位を保存。
- 元の C・D の前三角性を明示入力に、実 gluing 円錐・全整数シフト代表と、その全 dg 自然な Yoneda 加群比較を構成。
  同じ比較射の擬同型性・射影性から K の代表同型を得る。augmentation と両成分の移送比較も同じ射に保持する。
- `dgGluing_isDGPretriangulated` は、代表加群の同型閉包の零・全整数シフト・任意 distinguished 円錐閉性から実 gluing の前三角性を結論する。
  閉斉次シフト単位と円錐の指定境界元を使い、点ごとの同値を全 dg 自然な加群比較で実現している。
- 工程 (b) 進行中。片側が H⁰ で零となる対象の実充満 dg 部分圏 `DGGluingCFactor`・`DGGluingDFactor` と両包含・制限射影を構成。
  元の前三角性からホモトピー零対象を選び、両制限射影の実対象での全射性を証明。厳密零対象・零 Hom の仮定は追加しない。
- C 因子への左 Hom 射影、D 因子からの右 Hom 射影は擬同型。両充満因子と元の C・D の dg 準同値を証明。
  `dgGluingFactors_semiorthogonal` は順序 ⟨D,C⟩ の実 Hom 複体の全次数 acyclic 性。
- 同じ制限射影を順関手とする両 H⁰ 同値と、その逆による C・D 切断関手を構成。切断後の射影は実余単位で恒等と自然同型。
  元の Hom 射影の全単射から、左射影 ⊣ C 切断、D 切断 ⊣ 右射影の実 H⁰ 随伴を構成。
  C 随伴の余単位と D 随伴の単位は同じ切断同型の順射・逆射で可逆。両切断の完全忠実性も供給。
- D 随伴の同じ余単位を実閉 gluing 射へ持ち上げ、その右成分が H⁰ で同型と証明。実円錐は C 因子に属する。
  左零成分を持つ始域の円錐の左成分を標的の左成分と H⁰ で同定し、C 因子同値で円錐を同じ C 切断へ同定。
- `dgGluingDecompositionTriangle` は各実対象 X について、D 切断→X→C 切断の代表加群を三対象に持つ K(Gluing) の distinguished 三角形。
  第一射は同じ D 随伴余単位の Yoneda 像。元の H⁰ に未導入の三角構造や ∞ 随伴を結論していない。
- C 因子上の制限 Hom 加群値 dg 関手と、両射影で制限した係数 M[-1] の dg 関手を構成。
  標準 bottom 包含は全因子対で擬同型。両 Hom 射影は零、第三成分は恒等。比較元零の仮定なし。
- comma 合成の第三成分を左右の全次数作用と Koszul 符号で記述し、bottom の左右作用の場合も供給。
  係数比較を全 dg 自然な加群射・関手間比較へ束ねる段階が未完。(b) 継続中、(c)〜(f) は未着手。

### 主要宣言
- `DGGluingObject`・`dgGluingDifference`・`dgGluingHomComplex`・`dgGluingHomPrimitive_boundary`
- `dgGluingHom_d_comparison`・`dgGluingHom_ext`・`dgGluingHomLift_unique`・`dgGluingAugmentation_value`
- `DGGluingRepresentableCategory`・`dgGluingRepresentableRight`・`dgGluingRepresentableLeftModule`
- `dgGluingHomRepresentableIso`・`dgGluingHomRepresentableIso_left`・`dgGluingHomRepresentableIso_right`
- `dgGluingDGCategory`・`dgGluingToComma`・`dgGluingLeft`・`dgGluingRight`
- `dgGluingLeft_comp_yoneda`・`dgGluingIdentity`・`dgGluingComposition`・`dgGluingHomComparison_yoneda`・`dgGluingIdentity_comparison`
- `dgGluingConeSquareMatrix_eq`・`dgGluingConeCoconeIso`・`dgGluingHomConeKernelIso_inl`
- `dgGluingComposition_comparison`・`dgGluingPostcomposition_comparison`・`dgGluingPostcomposition_fst`
- `dgGluingCommaClosedSquareHomotopy_equation`・`dgGluingConeCoefficient`
- `dgGluingCommaConeElement_closed`・`dgGluingCommaConeMorphism_eval`・`dgGluingConeMorphism`
- `dgGluingKernelConeIso`・`dgGluingKernelConeIso_inr`・`dgGluingCommaKernelConeIso`
- `dgGluingKernelColumnIso_hom_naturality`・`dgGluingKernelHomAction_yoneda`・`dgGluingKernelHomConeAction_inl`
- `dgGluingYonedaConeIso_canonical`・`dgGluingHomConeRightTensorTargetIso`・`dgGluingHomConeRightCoefficient_kernel_module`
- `DGGluingConeRepresentative`・`dgGluingChooseConeRepresentative`
- `dgGluingConeObject`・`dgGluingConeObject_augmentation`・`dgGluingConeObject_leftIso`・`dgGluingConeObject_rightIso`
- `dgGluingConeObject_augmentation_transport`・`dgGluingConeRightHomotopyIso`
- `dgGluingHomConeKernelIso`・`dgGluingKernelConeRepresentativeMap`・`dgGluingKernelConeRepresentativeMap_source_homotopy`
- `dgGluingCoconeExtract_isIso`・`dgGluingCommaPostHomotopy_isIso`・`dgGluingHomConeKernelRepresentativeEquiv`
- `dgGluingKernelHomIso`・`dgGluingKernelHomIso_identity`・`dgGluingHomConeNativeEquiv`
- `dgGluingCommaToKernel`・`dgGluingKernelHomIso_factorization`・`dgGluingToKernelComma`・`dgGluingKernelHomIso_composition`
- `dgGluingSmall`・`dgGluingKernelConeInr`・`dgGluingConeInr`・`dgGluingHomConeKernelIso_inr`
- `dgGluingConeNullCochain`・`dgGluingConeModuleNullElement_boundary`・`dgGluingConeModuleMap`・`dgGluingChosenConeModuleMap`
- `dgGluingConeModuleMapEvaluation_inl`・`dgGluingConeModuleMapEvaluation_inr_comparison`・`dgGluingConeNullElement_kernel`
- `dgGluingConeModuleMapEvaluation_eq`・`dgGluingConeModuleMap_quasiIso`・`dgGluingConeModuleHomotopyIso`
- `dgGluingConeHomotopyRepresentable`・`dgGluingChosenConeHomotopyRepresentable`
- `dgGluingZeroHomotopyRepresentable`・`dgGluingZeroObject`・`dgGluingZeroRepresentableIso`
- `dgGluingRepresentableProperty_shift_nat`・`dgGluingRepresentable_containsZero`・`dgGluingRepresentable_isTriangulatedClosed₃`
- `DGGluingShiftRepresentative`・`dgGluingChooseShiftRepresentative`・`dgGluingShiftRepresentativeHomInv_homotopy`
- `dgGluingShiftObject`・`dgGluingShiftObject_augmentation_transport`・`dgGluingKernelShiftRepresentativeMap`
- `dgGluingKernelShiftRepresentativePostEquiv`・`dgGluingNormalizedShiftSquare`・`dgGluingKernelShiftProjection_closed`
- `dgGluingKernelShiftInclusion_closed`・`dgGluingKernelShiftOutIn`・`dgGluingKernelShiftInOut`
- `dgGluingKernelHomModuleShiftIso`・`dgGluingKernelRepresentableModuleIso`・`dgGluingChosenShiftModuleMap`
- `dgGluingShiftModuleMap_quasiIso`・`dgGluingChosenShiftHomotopyRepresentable`・`dgGluing_isDGPretriangulated`
- `DGGluingCFactor`・`DGGluingDFactor`・`dgGluingFactorZeroObject`・`dgGluingCFactorProjection`
- `dgGluingCFactorProjection_quasiEquivalence`・`dgGluingLeftHomMap_quasiIso_of_target_right_zero`・`dgGluingFactors_semiorthogonal`
- `dgGluingDFactorProjection_quasiEquivalence`・`dgGluingCFactorHomotopyEquivalence`・`dgGluingDFactorHomotopyEquivalence`
- `dgGluingCProjectionAdjunction`・`dgGluingDProjectionAdjunction`・`dgGluingCSectionHomotopyFullyFaithful`・`dgGluingDSectionHomotopyFullyFaithful`
- `dgGluingDecompositionArrow`・`dgGluingDecompositionCFactor`・`dgGluingDecompositionCSectionIso`
- `dgGluingDecompositionTriangle`・`dgGluingDecompositionTriangle_distinguished`・`dgGluingDecompositionTriangle_mor₁`
- `dgGluingCrossHomFunctor`・`dgGluingCrossCoefficientFunctor`・`dgGluingCrossHomCoefficientMap_quasiIso`
- `dgGluingCrossHomCoefficientMap_primitive`・`dgGluingCommaForward_primitive`

### 残り（依存順）
1. (b) 残り：gluing 関手の全次数係数 M[-1] と自然性の同定。充満因子・半直交性・両 H⁰ 随伴・K の分解三角形は構成済み。KL §4.2。見積り 1 日。
2. (c) dg nerve の二射影と構造変換、F2 の laxPullback への比較写像。Tamme Definition 5。見積り 1〜2 日。
3. (d) 比較の充満忠実性・本質的全射性と全試験関手の ∞ 普遍性。Tamme Remark 6、F0 判定。見積り 2〜3 日。
4. (e) 安定性・完全射影と F2・K-8b の半直交分解との整合。Tamme Lemma 8。見積り 1 日。
5. (f) 通常 pullback と Verdier 商 ⊙ の dg 同定、Sp の K-8d8 への `IsVerdierSequence` の供給（D と共同）。
   Tamme §1、Drinfeld Thm 3.4、β3 の平坦商。見積り 2〜3 日。

### 依存と提供
- 読み取り専用：`InfinityCategories/Derived/`（β5 の D(A)、双加群、相対 tensor、Drinfeld 商 β3）、`InfinityCategories/F2/`（lax pullback、安定性）、`InfinityCategories/Core/`・`F1/`。
- 提供先：Sp（K-8 の ⊙ の同定）、K-F・K-S•（Verdier 列の具体例）。
- β5 の確認済み入口：`dgAlgebraDerivedInfinityCategory`（`DGAlgebraDerivedInfinity`）、
  `Bimodule`（`DifferentialGraded/Bimodule/Basic`）、`Morita.kernelTensor`（通常 tensor）、
  `dgKernelDerivedInfinity`（半自由入力・実出力分解を保つ導来 tensor）。

### 次の一手
- `dgGluingCommaForward_primitive` と bottom の二射影零・第三成分恒等を使い、係数包含の左右の全次数自然性を証明する。
  native/comma Hom 同型と全 Yoneda Hom を通して元の M の作用へ戻し、−1 シフトの Koszul 符号を照合する。
  同じ比較を全 dg 自然な加群射・dg 関手間比較へ束ね、構成済みの各評価の擬同型性を供給する。

### 未コミット・既知の問題
- 217モジュール・集約ビルド成功（5138 jobs）、公理監査3662宣言成功。許容三公理のみ。所有警告・新規 sorry・axiom・主経路 `ModelCategory` 仮定なし。
  公開22署名を検査済み。新規7モジュール、集約・監査・本計画の専有10パスだけを保存。他レーンの差分は含めない。
  前三角性は元の両圏について明示入力に取り、gluing の前三角性・安定性を仮定に追加していない。
- β5 の `Bimodule` は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`。
  KL の (D₂ᵒᵖ ⊗ D₁)-dgm は右 dg 加群の規約。比較差は `gμ − νf` を保持する。

## 規約
- 配置 `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約 `Derived/Gluing.lean`、監査 `scripts/audit_derived_gluing.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts（categorical resolutions, gluing）、Drinfeld 2004。
