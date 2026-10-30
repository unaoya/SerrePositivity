# HomologicalAlgebra の整理計画（2026-10-30）

概要：論文の層の見直しのうち、`SerrePositivity/HomologicalAlgebra/`（551 ファイル、約 57200 行。トップ階層 356、DerivedCompletion/ 192、
ComplexLimits/ 3）について、ファイルの統合、未使用の宣言の削除、Mathlib への置き換え、重複の一本化、Mathlib への提出候補をまとめる。
群ごとの調査（2026-10-30、読むだけ、5 群並列）の結果を元にした計画で、実作業はまだ行っていない。
方針：作業の決まりは [commutative-algebra-refactor-plan.md](commutative-algebra-refactor-plan.md) の §2 と同じ。BhattScholze への露出が
CommutativeAlgebra よりずっと大きいので、作業を「BS に触れない層」と「BS の再ビルドを伴う層」に分ける（§7）。
規約：Mathlib の確認は固定版（2026-10-07）と最新版（2026-10-28）の両方で行った。差があったのは StupidTruncation だけ（§2.2）。
`sorry`・`axiom`・`admit`・外せない仮定（`[ModelCategory …]` など）は 5 群のどこにもなかった。
使われ方：作業を再開するときの手順書。

## 1. 群の分け方と外への影響

| 群 | 内容 | ファイル数 | 行 | BS が直接 import するファイル |
| --- | --- | --- | --- | --- |
| HA1 | 複体の基礎：Cochain*・テンソル・錐・切り詰め・冪等元・BoundedAbove・分解・線形 Yoneda・列の余極限 | 136 | 約 14000 | 少数（BoundedAboveDerivedAssociator・BaseChange、KProjectiveLift、RestrictedBaseChangeScalar、CompatibleRootQuotientTor、SequentialComplexColimits） |
| HA2 | 導来テンソル・導来代数・H⁰ の環・純な導来 Cartier・導来平坦性 | 105 | 約 12500 | 約 20 |
| HA3 | Koszul・Tor・局所コホモロジー・基底変換・有限自由分解・Auslander–Buchsbaum | 118 | 約 12500 | 約 18 |
| HA4 | DerivedCompletion の塔の側：Tower・Milnor・Koszul 塔・Principal・Pair・Power・Restriction・IteratedTensor | 88 | 約 9500 | 約 20 |
| HA5 | DerivedCompletion の完備化の側：Module 完備・ComplexCompletion・BoundedAbove 完備化・完備テンソル・完備代数の H⁰・ModulePower | 104 | 約 10000 | 31 |

- BS が多く使う名前：`IsModuleComplete`（BS 35 ファイル・CLMST 14）、`PDCompletionH0`・`pdCompletionUnit`・`pdCompletionCommRing`（BS 33）、
  `boundedAboveDerivedBaseChange`（BS で 557 回）、`boundedAboveDerivedCompletionFunctor`（BS 18）、`derivedComplexCompletionFunctor`（BS 13・CLMST 9）、
  `PrincipalCompletionH0`（29 回）、`principalCompletionCommRing`（22 回）、`pairKoszulCoordinates`（16 回）。これらは名前を変えない。
- PerfectComplex にも CochainTensor 系がある（[perfect-complex-refactor-plan.md](perfect-complex-refactor-plan.md)）。本体は HA に置く（§8 の 3）。

## 2. HA1 複体の基礎（136 → 約 20 ファイル）

### 2.1 統合

| 新しいファイル | 元のファイル |
| --- | --- |
| Complex/Basic | Basic・CochainBiproduct・CochainKernelLift・CochainTwoTermScalarMap（ProjectiveBaseChange は削除） |
| Complex/Cone | CochainConeArrowMap・ConeCoordinates・ConeNaturality・ConeAdditiveNaturality・ConeProduct・ConeTriangle（Mathlib の MappingCone だけ） |
| Complex/ConeLES | ConeLES・CochainAcyclic（ConeLES は importer 16 本なので軽く保つ） |
| Complex/Truncation | StupidTruncation・TruncationBoundary・NullHomotopy |
| Complex/Idempotent | CochainIdempotent と Acyclic・Decomposition・Sum・FiniteSum・Functor・Homology・Iso・QuasiIso・ShortExact・Trivial（約 780 行） |
| Tensor/Basic | CochainTensor と Linear・DegreeMaps・Bounds・Finite・Projective・Symmetry・Homotopy・Shift、CochainIdempotentTensor |
| Tensor/Coherence | Shuffle・Homogeneous・Triple・TripleDifferential・TripleDegreeMaps・Hexagon・Braided・ShuffleEquivariance・ScalarCoordinates・Six*（約 1100 行、Triple と Six に分けてもよい） |
| Tensor/Exactness | ShortExact・TripleShortExact・Single・Cone・Acyclic・BoundedAbove |
| Tensor/BaseChange | CochainTensorBaseChange・BaseChangeSymmetry・TripleBaseChange・BaseChangeSingle・RestrictedBaseChangeComplex（RestrictedBaseChangeScalar は重いので別） |
| Tensor/SingleMonoidal | CochainSingleTensorComparison・CochainSingleMonoidal・CochainDiscreteAlgebra（MonoidalUnitHomRing・MonoidalPointAction は圏論なので HA の外へ） |
| Tensor/ScalarCone | CochainTensorScalarCone・LinearFunctorScalarCone（Koszul を import するので軽いファイルに混ぜない） |
| KProjective | KProjectiveLift・KProjectiveCohomologyLinear |
| BoundedAbove/Derived | ProjectiveResolution・ResolutionFunctor・DerivedModels・LeftDerived・DerivedAdditive・DerivedShift・DerivedCone・DerivedConeTriangle・SourceConeTriangle（ExactDerived は任意） |
| BoundedAbove/Tensor | TensorModels・TensorFunctor・DerivedTensor・DerivedAssociator・DerivedUnit・DerivedBaseChange（DerivedModule・DerivedAcyclic・DerivedTruncation は重い層を引くので別のまま） |
| Resolution | Resolution・ResolutionNaturality・ResolutionMappingCone・ConeResolution・BoundedResolutionDimension |
| LinearYoneda | ChainLinearYoneda・InjectiveLinearYoneda・ProjectiveLinearCoyoneda・ChainLinearYonedaZero・ProjectiveExtNaturality・ProjectiveResolutionInjectiveAcyclic・CochainLinearDual・MappingConeLinearDual・CochainLinearDualCone |
| ComplexColimits | SequentialComplexColimits・ExactChainHomologyColimits・ExactFunctorColimits・LinearFunctorColimits |
| Ext/LocalCohomology | ProjectiveExtSequence・ProjectiveExtColimitExact・InjectiveCoefficientDimensionShift・GeneralKoszulLocalCohomology・GeneralLocalCohomologyBaseChange |
| MinimalResolution | MinimalFreeResolution・MinimalBetti・MinimalTruncation・MinimalBoundary |
| ScalarConeAnnihilators | TwoTermConeAnnihilator・ConeComparisonSquare・ConeOfSurjectiveSource・ConeFiniteCover・TwoCohomologyAnnihilator（後ろの 2 本は重いので層の最後で） |

- 他の群へ回す：CompatibleRoot{Family,FiniteFamily,Quotient}Tor → HA3 の Tor。ModelTensorFlatCriterion・ModelTensorHomologySurjective → HA2 の導来平坦性。
  BoundedKoszulAugmentation・BoundedTermKoszulAcyclic → HA3 の Koszul。ChainAugmentationNormalization・CochainAugmentationModels → HA2 の augmentation。
- 層の逆転：`ComplexLimits/*`（3 本）は KST.LocalizingInvariants を import し、名前空間は `SerrePositivity.EInfinity.ComplexLimits`。
  `EInfinity/ComplexLimits/*` は再エクスポートの殻だけ。1 本にまとめて EInfinity 側へ移し、殻を消す。
- Basic.lean が `HomotopyCategory.MappingCone` と `Noetherian` を import していて、importer 15 本に重さを渡している。Resolution.lean の
  `Mathlib.Data.Real.Basic`・`Mathlib.Tactic.Ring` も不要に見える。統合のときに import を絞る。

### 2.2 Mathlib との重なり

- StupidTruncation の `above`・`below`・`inclusion`・`projection`・`inclusion_f_isIso`・`projection_f_isIso` → `HomologicalComplex.stupidTrunc`・
  `ιStupidTrunc`・`πStupidTrunc`・`isIso_ιStupidTrunc_f`・`ιStupidTruncNatTrans`（確度高）。**最新版にしかない**（固定版は `stupidTrunc` だけ）。
  **決定（2026-10-30）**：Mathlib を上げるまで保留。
- `ProjectiveBaseChange.projective_baseChange` は `infer_instance`（削除）。`CochainBiproduct` の instance は `HasFiniteBiproducts.of_hasFiniteProducts`。
  `CochainIdempotentQuasiIso.imageMap_quasiIso` は `quasiIso_of_retractArrow` の 1 行の包み。
- KProjective の持ち上げ 3 本（`BoundedAboveDerivedModels.exists_cochainMap_of_isKProjective`、`KProjectiveLift.exists_lift_of_quasiIso`、
  `homotopyOfDerivedMapEq`）は `IsKProjective.Qh_map_bijective`＋`quotientCompQhIso` の同じ議論。1 本にする。
  `kProjectiveCohomologyDerivedEquiv` は `CohomologyClass.equivOfIsKProjective` と `SmallShiftedHom.equiv` の合成（確度中）。
- `linearYonedaModule_preservesHomology` 系 → `preservesHomology_preadditiveYonedaObj_of_injective` 系（確度中。Mathlib は AddCommGrp 値）。
- `isZero_homology_of_isZero_X` → `ShortComplex.isZero_homology_of_isZero_X₂`、`projective_of_free` → `ModuleCat.projective_of_free`、
  `isZero_moduleCat_free` → `Module.Free.of_subsingleton`（いずれも確度中）。
- テンソル積（訂正）：`cochainTensor` などは Mathlib の `HomologicalComplex` のモノイダル構造（Algebra/Homology/Monoidal.lean）の薄い包み
  （`cochainTensor` = `tensorObj`、`cochainTensorMap` = `⊗ₘ`、`cochainTensorAssociator` = `α_`、`cochainTensorShuffle` = `tensorμ` など、確度高）。
  詳しくは [perfect-complex-refactor-plan.md](perfect-complex-refactor-plan.md) §3.2。Mathlib にないのは Koszul 符号付きの組みひも（`β_`）と
  `(tensor C).Braided`。
- Mathlib にないもの：複体の Koszul 符号付きの組みひも（Symmetry・Hexagon・Braided）、`MonoidalLinear`、`single₀` のモノイダル性、
  `restrictionFunctor`・`extendFunctor` の `Linear`、exact colimit と homology の可換、`Resolution.leftDerived_additive`、`DerivedCategory.Minus` 上の
  左導来関手（Mathlib の TODO にある）。

### 2.3 一本化

- SequentialChainHomologyColimits は ExactChainHomologyColimits の `J = ℕ` の写し。削除。
- ConeResolution の `coneHomologyZeroEquiv`・`isResolutionOf_cone` は ResolutionMappingCone の特殊化。
- `BoundedAboveDerivedModel` と `BoundedAboveProjectiveResolution` は `map`・`mapIdHomotopy`・`mapCompHomotopy`・`map_quasiIso` が並行。
- DegreeMaps と TripleDegreeMaps、Shuffle と SixShuffle は項数違いの同じ API。一般化は後回しでよい（記録だけ）。
- `TruncationBoundary.boundary` と `MinimalBoundary.boundary` は特殊化の関係で、名前空間違いの同名。

### 2.4 未使用

- BoundedAbove：`boundedAboveDerivedTensor{Associator,LeftUnitor,RightUnitor}NatIso`、`boundedAboveLeftDerived{Cone,}Triangle_homology_exact`、
  `boundedAboveLeftDerivedShiftNatIso`、`boundedAboveDerivedTensorComplexComparison`、`boundedAboveResolutionFunctor`、
  `boundedAboveDerivedTensorFunctor_map_isIso`、`boundedAboveDerivedTensorAugmentation`、`derivedTensorComparisonIso_augmentation`。
- 冪等元：`imageMap_id/_comp`、`ι_decompositionIso_hom`、`decompositionIso_inv_π`、`imageFiniteSumIso_hom_inclusion`、`imageFunctorIso_naturality`、
  `image_{finite,projective,isZero}_X`、`imageIsoOfMapEqId_hom/_inv` ほか。
- テンソル：`cochainSingleTensorIso_naturality`、`cochainTensor_d_comp_d`、`extendScalars_braiding_delta`、`cochainTensorSummand_isZero_right`、
  `tensorConeInlX_fst/_snd`、`cochainTensorConeTriangleIso`、`exists_cochainTensorX_finiteCoproductModel`、`cochainTensor_isZero_X_of_bounds`、
  `cochainTensorFixed{Right,Left}_commShift` ほか。
- 線形双対：`cochainLinearDualNonnegativeNatIso_complex_map`、`cochainLinearDualTermIso`、`cochainLinearDual_map_apply`、
  `mappingConeTargetHomEquiv_d_snd`、`scalarMappingConeTargetHomEquiv_d_fst` ほか。
- その他：`chainHomologyZeroProjection_descOpcycles`、`mono_homologyMap_liftSES_zero`、`generalKoszulLocalCohomologyComparison_map_eq_zero_iff`、
  `injectiveCoefficientHomologyNatIso_zero/_unique`、`chainLinearYonedaObjIsoMapOp`、`MinimalBetti.finrank_eq_length_tor`。
- instance と `@[simp]` は暗黙に使われうるので、削除の前にビルドで確かめる。HA の中に importer がないファイル（CochainIdempotent の一部、
  CochainTensor の Triple*・ShuffleEquivariance など、MinimalBoundary）は外の利用者を確かめる。

### 2.5 選択と構成

- `BoundedAboveProjectiveResolution.ofBoundedAbove`・`BoundedAboveDerivedModel.ofIsLE` は `Classical.choice`、`comparison`・`map`・`mapHomotopy` は
  存在定理の `.choose`。`IsKProjective` の持ち上げ（Mathlib の `equivOfIsKProjective`）から直接作る。BS が使う名前は残す。

### 2.6 提出候補

複体の対称モノイダル構造（`HomologicalComplex C c` へ一般化して）、`MonoidalPreadditive`・`MonoidalLinear`、`single₀` のモノイダル性、
`restrictionFunctor`・`extendFunctor` の `Linear`、exact colimit と homology の可換、関手の複体への転置、`QuasiIso f ↔ (mappingCone f).Acyclic`
（アーベル圏へ一般化して）、冪等鎖写像の像と分解、`Resolution.leftDerived_additive`、「homology が r で消える有界複体では r の冪が零ホモトピック」。

## 3. HA2 導来テンソル・導来代数（105 → 約 18 ファイル）

### 3.1 統合（import の順）

| 新しいファイル | 元のファイル |
| --- | --- |
| DerivedHomologyBasics | DerivedPureHomology・DerivedHomologyLinear（Mathlib だけ） |
| DerivedRestriction | DerivedRestriction・DerivedRestrictionConservative・AlgebraRestrictionSingle・AlgebraScalarExtensionModule、RingEquivDerivedTensor の `derivedRestrictScalars_isGE_iff/_isLE_iff` |
| ClassicalDerivedTensor | DerivedTensor・DerivedTensorRealization・DerivedTensorModuleResolution・DerivedTensorBaseChange・ScalarExtensionTensorCancellation |
| UnitHomology | UnitLinearHomComplex・DerivedUnitHomology・UnitHomologyNaturality・DerivedUnitHomologyNatural |
| TensorComplexNaturality | TensorBaseChangeNaturality・TensorConeNaturality・TensorSingleNaturality |
| DerivedTensorMonoidal | DerivedTensorCoherenceModels・Triangle・Pentagon・Monoidal・Symmetry・Braided・Linear（一本の鎖） |
| DerivedTensorModules | DerivedBaseChangeTensor・DerivedTensorModuleModels・ModuleComparison・TorNaturality・UnresolvedModule・DerivedNonpositiveHom・DerivedTensorNonpositive・ModuleNaturality・DerivedFlatModelTensor |
| DerivedTensorAugmentation | DerivedTensorAugmentationModels・DerivedBaseChangeAugmentationModels・…Comparison・DerivedBaseChangeTensorAugmentation・AlgebraBaseChangeTensorAugmentation・DerivedTensorFixedModuleModel |
| DerivedAlgebraObjects | DerivedDiscreteAlgebraMaps・DerivedSingleTensorSymmetry・DerivedSingleTensorUnit・DerivedAlgebraAssociativity・DerivedAlgebraObjects・DerivedAlgebraMorphisms・DerivedTensorAlgebraAugmentation |
| DerivedH0Ring | DerivedH0Algebra・UnitHomologyNormalization・DerivedSingleH0Algebra・DerivedTensorH0Algebra・DerivedTensorH0Coefficient・DerivedDiscretePointAction・DerivedRestrictionNormalization・DerivedRestrictionSingleH0・AlgebraBaseChangeTensorH0 |
| DerivedTensorCompletionAlgebra | DerivedTensorAugmentationIso・DerivedTensorAlgebraCongruence・RingEquivDerivedTensor（DerivedCompletion を import するので DerivedH0Ring と分ける） |
| DerivedQuotientBaseChange | DerivedBaseChangeDiscrete・DerivedQuotientBaseChange・DerivedBaseChangeRightTensor・DerivedQuotientH0Normalization・DerivedQuotientTensorAugmentation・QuotientSupTorComparison |
| DerivedKoszulCones | DerivedModuleCone・ScalarConeModuleQuotient・DerivedQuotientKoszul・DerivedKoszulDescent・DerivedScalarConeBaseChange・DerivedTensorKoszul・ScalarConeShiftNaturality |
| PureDerivedCartier | PureDerivedCartier{Quotient,Naturality,Single,Representatives,ModuleRepresentatives}・DerivedTensorPureFactorization・DerivedTensorCartierProducts |
| DerivedFlatness | DerivedAcyclicSingle・DerivedAcyclicHomology・NilpotentDerivedReduction・ScalarExtensionTensorTests・FlatDerivedPowerReductions（CompletedFlat* 3 本は DerivedCompletion を引くので別ファイル） |
| AlgebraKoszulDual | AlgebraLinearYoneda・…BaseChange・AlgebraMappingConeDual・AlgebraKoszul{Dual,Colimit,Bounds,Augmentation,AugmentationZero,TermColimit}・AlgebraEquivariantShortComplex |
| FlatKoszul | FlatBaseChange・FlatKoszulFiniteness（CLMST が使う） |
| ModuleTorsion | IdealPowerTorsion・IdealPowerTorsionSupport・IdealPowerTorsionBaseChange・NilpotentModuleFiltration・ScalarWeightedColimit・QuotientTorOneConormal |

- DerivedRestrictionNormalization・DerivedRestrictionSingleH0 は UnitHomologyNormalization 経由で DerivedTensorBraided を引くので DerivedRestriction に入れない。
- `koszulModuleFunctor_self_eq` は FlatKoszulFiniteness にあるが一般の Koszul の補題（HA3 へ）。
- `maxHeartbeats` を上げているファイル：DerivedQuotientTensorAugmentation・PureDerivedCartierNaturality（800000）、DerivedTensorPentagon（600000）。
  統合のときは節ごとに `set_option … in` にする。

### 3.2 Mathlib との重なり

- 導来テンソル、`DerivedCategory` のモノイダル構造はどちらの版にもない。DerivedTensorMonoidal 以下は置き換えられない。
- `derivedTensor` は `((tensoringLeft _).obj M).leftDerivedToHomotopyCategory.obj N` の薄い包みで、`derivedTensor_homology_eq` は Mathlib の
  `Tor`（Monoidal/Tor）の定義そのもの（確度高）。
- `derivedRestrictScalars`・`…Factors`・`…SingleIso` は `Functor.mapDerivedCategory`・`mapDerivedCategoryFactors`・`mapDerivedCategorySingleFunctor`
  の 1 行の別名（確度高。BS が名前を使うので残し、定義を `abbrev` に）。
- `flat_of_algebra_isPushout` → `Module.Flat.isBaseChange` 系（確度中〜高、CLMST が使う）。`scalarExtensionTensorCancelIso` は
  `AlgebraTensorModule.cancelBaseChange` の圏論的な包み（確度中）。

### 3.3 一本化

- **導来テンソルが 3 通り**：`derivedTensor`（ℕ ホモトピー圏）、`realizedDerivedTensor`、`boundedAboveDerivedTensor`。比較のためだけのファイル
  （DerivedTensorModuleComparison・DerivedTensorFixedModuleModel）がある。長期には `boundedAboveDerivedTensor` に寄せる。前の 2 つは BS が名前を
  使う（`derivedTensor`・`IsConcentratedInDegreeZero`・`realizedSingleH0Iso`）ので、すぐには消さない。`realizedDerivedTensorHomologyIso` と
  `derivedTensor_homology_eq` は Tor の同定の言い直しで、ファイルの外で使われていない。
- DerivedUnitHomology の `derivedUnitHomologyLinearEquiv`・`derivedUnitH0HomLinearEquiv` は Natural 版と重複。Natural 版だけ残す。
- `derivedModuleBaseChange*`（DerivedTensorBaseChange）と `boundedAboveDerivedBaseChangeModule*`（HA1 の BoundedAboveDerivedModule）が並行。両方 BS が使う。
- H⁰ の正規化が 4 系統（UnitHomologyNormalization、DerivedRestrictionNormalization＋SingleH0、DerivedQuotientH0Normalization、HA3 の
  RealizedSingleH0Normalization）。共通の補題で書けるか、統合のときに確かめる。

### 3.4 未使用（全 105 ファイルを名前で走査。instance と `@[simp]` は除く）

`algebraKoszulDualColimitAugmentation_ι`、`parameterKoszulColimitAugmentation`、`algebraKoszulDualIntegerLocalCohomologyComparison`、
`parameterKoszulColimit_isZero_X_above/_below`、`boundedAboveDerivedAlgebra_mul/_one`、`boundedAboveDerivedTensorAlgebra_X`、
`boundedAboveDerivedTensorBaseChangeModuleIso_naturality`、`restrictedDerivedTensorBaseChangeRightNatIso`、`derivedH0AlgMap_id`、
`derivedKoszulHomology_uniform_annihilated_iff`、`derivedKoszul_homologyTorAcyclic`、`moduleMapConeScalar_eq_zero_annihilates_ker`、
`derivedTensorQuotientModuleIso_naturality`、`boundedAboveDerivedAlgebraIso`、`boundedAboveCompletedTensorAlgebraIso_left/_right`、
`realizedDerivedTensorH0Iso`、`realizedDerivedTensor_discrete_iff`、`primaryComponent_eq_of_radical_eq`、`pureDerivedAlgebraCartierQuotient_pure`、
`completedTensorModulesRingEquivRestriction_homology_isZero_iff` ほか（調査メモの全リストを作業時に再確認する）。

### 3.5 選択と構成

- `normalizedPureHomologyIso := (exists_normalizedPureHomologyIso X i).choose`（BS・CLMST が使う）。一意性は証明済みなので標準的だが、展開できない。
  t 構造の切り詰めから直接作るか、このまま残すかを決める。
- `quotientTorOneConormalEquiv` は `Classical.choice (nonempty_torModule_one_equiv_ker …)` で作られ、同型が標準的でない（BS が使う）。
  連結写像から構成的に作り直す。Mathlib に出すならこれが前提。

### 3.6 提出候補

`DerivedCategory.homologyFunctor` の `Linear`、純な対象と `singleFunctor` の標準同型（DerivedPureHomology）、`Ideal` の冪ねじれ関手と根基への
非依存性、`Hom(R/I, M) ≃ₗ torsionBySet M I`、`Tor₁(R/I, R/I) ≅ I/I²`（構成的にしてから）、冪零フィルトレーションの補題、`derivedRestrictScalars`
が同型を反映すること。`DerivedCategory.Minus (ModuleCat R)` のモノイダル構造は価値が高いが大仕事。

## 4. HA3 Koszul・Tor・局所コホモロジー（118 → 約 20 ファイル）

### 4.1 統合（import の順）

| 新しいファイル | 元のファイル |
| --- | --- |
| ModuleBaseChange | BaseChange・ModuleBaseChangeTensor・ModuleScalarExtensionAnnihilator・FiniteFreeBaseChange |
| ModuleCatColimits | ColimitLinearFunctor・FiniteSupportCoproduct・FiniteSupQuotientColimit |
| Tor/Basic | Tor・TorUniformAnnihilator・BaseChangeEquivalence（BaseChange は importer 12 本なので Tor に入れない） |
| Tor/LongExact | TorLES・TorNaturality・TorSymmetry・LeftDerivedZeroFunctorNaturality・CoefficientDimensionShift |
| Tor/Flatness | LocalFlatnessCriterion・TorDimensionShift・TorFlatBaseChangeVanishing・TorBaseChange（`torModule_subsingleton_*` の一般の補題は Tor/Basic へ） |
| Tor/Length | TorFiniteLength・TorFiniteLengthBound・TorTwoRingComparison・KoszulTorLength・KoszulOrdinaryLength |
| Koszul/CoefficientFunctor | DirectedHomology・KoszulDirectedLimit・KoszulScalarControl・KoszulCoordinateControl・KoszulModuleBounds・KoszulIdealAction・KoszulRadicalSupport・KoszulRestriction・KoszulOneCoordinates・KoszulWeightedColimit |
| Koszul/Towers | KoszulTower・KoszulTruncation・KoszulDirectedUnion・HomologyQuotient |
| Koszul/TorComparison | KoszulTorComparison・KoszulTensorConeComparison・KoszulAlgebraTorComparison・TorCoefficientIdeal・TorAlgebraScalarComparison・TorAlgebraNaturality |
| Koszul/ParameterAnnihilators | KoszulHomologyAnnihilator・ParameterKoszulComparison・ParameterKoszulIdempotent・FiniteParameterKoszulAnnihilator・TorFiniteFreeComparisonAnnihilator・TorAlmostComparisonTransport |
| Tor/Colimits | TorSequentialColimits・TorExactColimits・TorFiniteCoefficients・BalancedTorResolution・ModuleTensorChainFunctor |
| Tor/AcyclicBaseChange | TorAcyclicBaseChangeResolution・…Comparison・TorAlgebraAcyclicBaseChange・FiniteCohomologyBaseChange・PrincipalQuotientResolution・RegularPrincipalTor・PowerTorsionTorBaseChange |
| Tor/FlatDescent | FaithfullyFlatDerivedHomology・PowerTorsionDerivedDescent・TorCoefficientPowerTorsionDescent・PowerTorsionCompletedBaseChange・CompleteTwoCohomologyAnnihilator・CompleteFaithfullyFlatDescent |
| Tor/PerfectRings | PerfectRadicalQuotientTor・PerfectRingTor・PerfectResidueTensorRegular |
| Koszul/LinearDuality | KoszulLinearDuality・…Naturality・NonnegativeCochainHomology・HomComplexCone・KoszulBaseChangeNaturality |
| LocalCohomology/KoszulComparison | ExtZeroComparison・KoszulExtComparison・LocalCohomologyKoszulPowers・…Comparison・KoszulDualZero・…Transitions・…Torsion・KoszulDualCoefficientExact・KoszulDualInjectiveAcyclic・ArtinReesHomology・KoszulTransitionDepth・KoszulDualBaseChange |
| LocalCohomology/Actions | KoszulDualTorComparison・LocalCohomologyAction・KoszulLocalCohomologyAction・LocalCohomologyScalarBaseChange・LocalCohomologyTorAnnihilator・ParameterLocalCohomologyAnnihilator・LocalCohomologyZeroTorsion |
| Resolution/FiniteFree | FiniteFreeResolution・RegularLocalResolution・LocalizedRegularResolution・FiniteLocalizationDescent・FiniteResolutionTrace・ControlledHorseshoe・ControlledResolution |
| AuslanderBuchsbaum | AuslanderBuchsbaum・RegularQuotientProjectiveDimension（§4.2） |
| ComplexUtilities | ModuleSubcomplex・AdicFilteredComplex・UniformNullHomotopy・SupportNullHomotopy・MapExtend・CoaugmentedReflection・ModuleTensorCochain{Filtration,Exact}（軽い側）と SingleTriangleExactReflection・RealizedSingleH0Normalization（導来圏側）に分ける |

- 循環の危険：KoszulDualTorComparison は KoszulExtComparison を import し、KoszulDualBaseChange は KoszulBaseChangeNaturality を import する。
  Koszul/LinearDuality → LocalCohomology/KoszulComparison → LocalCohomology/Actions の順を守る。
- `torCoefficientScalarEndomorphism`（BS・CLMST が使う Tor の係数作用）は KoszulTorComparison にある。Tor/Basic か Tor/LongExact へ移す（名前は残す）。
- 死んだファイル：KoszulHomologyLength（LengthAlgebra の再エクスポートのみ）、LocalCohomologyZeroBaseChange、PerfectQuotientTorOne、
  PowerResidueDerivedHomology（どれも importer は `SerrePositivity.lean` だけ）。
- HA1 から CompatibleRoot*Tor・BoundedKoszul* を受け入れる。HA4 の PowerTorsionTor* も Tor 側が自然（§5.1）。

### 4.2 Mathlib との重なり

- Koszul 複体、Auslander–Buchsbaum、左導来関手の長完全列、加群の Tor の包み、Tor の対称性は、どちらの版にもない。
- `free_baseChange`・`finite_baseChange` は `infer_instance` の包み（確度高、インライン化）。
- `ModuleCat.free_of_projective_of_isLocalRing` → `Module.free_of_flat_of_isLocalRing`（確度高）。
- `torModule_free_succ_eq_zero`・`torModule_pi_self_subsingleton` → `isZero_Tor_succ_of_projective` の 1 行の系（確度高）。
- AuslanderBuchsbaum・RegularQuotientProjectiveDimension は Mathlib の PR（commit 9c971a55）からの写しで、どちらの版にもまだない。
  主定理 `auslanderBuchsbaum` も `projectiveDimension_eq_regularQuotient` も未使用。名前に typo（`finte_free_ext_vanish_iff`）、
  ルート名前空間の一般の補題（`smul_prod_of_smul`・`subsingleton_of_pi`・`basis_lift` など）、`AuslanderBuchsbaum`/`auslanderBuchsbaum` の大小違いの対がある。
  **決定（2026-10-30）**：削除する（AuslanderBuchsbaum・RegularQuotientProjectiveDimension のファイルごと。利用者がないことを作業時に再確認）。
- `flat_of_torModule_one_residueField` は A = B・有限表示なら `Module.free_of_lTensor_residueField_injective` 系で足りる。A→B の一般形は Mathlib にない（確度中）。
- ExtZeroComparison は `Ext.homEquiv₀`・`Ext.linearEquiv₀` と重なる（確度中）。DirectedHomology は `ModuleCat.AB` の filtered colimit の完全性から出せる見込み（確度中）。

### 4.3 一本化

- `moduleCatBaseChangeTensorEquiv`（ModuleBaseChangeTensor）≡ `extendScalarsObjEquivTensor`（TorBaseChange、BS が使う）。後者を残す。
- `torModule_smul_eq_zero` ≈ `Tor.annihilator_le_torModule_right`。`torModule_one_subsingleton_of_exact` は `torModule_subsingleton_of_exact` の n = 1。
  `torModule_subsingleton_of_linearEquiv` ≈ `Tor.torAlgCongr`。PerfectQuotientTorOne は PerfectRadicalQuotientTor の i = 1。
  `length_homology_koszul_equiv` は `length_homology_baseChange_equiv` の特殊化。
- Koszul と Tor の比較が 3 系統（KoszulTorComparison・KoszulTensorConeComparison・KoszulAlgebraTorComparison）。それぞれの `_scalar_eq_zero_iff`・
  `_of_tor_annihilated`・`*PowersComparison` の多くは未使用。
- 忠実平坦の降下の骨組みが 3 回（FaithfullyFlatDerivedHomology・PowerTorsionDerivedDescent・PowerResidueDerivedHomology）。

### 4.4 未使用（639 宣言を名前で走査）

上の死んだファイルのほか：`coaugmentedHomEquiv_apply/_symm_apply`・`coaugmentedHom_ext`・`_naturality_left/right`・`coaugmentedHomEquivOfIsIso`、
`complete_two_cohomology_scalar_pow_eq_zero`、`complete_moduleMapConeScalar_pow_eq_zero`、`faithfullyFlatDerivedHomology_scalar_eq_zero_iff`、
`homologyZeroDesc_epi`・`coordinateQuotient_epi`・`minimalHomologyZeroQuotient_epi`、`koszulExtPowersComparison`、`koszulTorPowersComparison`、
`koszulModuleTorPowersComparison`、`koszulTorComparisonEquiv`、KoszulRadicalSupport の 2 定理、`regularKoszulLocalCohomologyComparison`、
`perfectRing_derivedTensor_concentrated(_of_char_eq_zero)`、`perfectRing_derivedTensorAlgebraAugmentation_isIso`、`torAlgebraComparisonNatIso`、
`length_torModule_comm`、`shortExact_iff_exists_distinguished_single_triangle` ほか。これらを消すと、ファイルの中だけで使われている補助
（LocalFlatnessCriterion の 8 個、TorSymmetry の `torOneKernel*`・`torShift*` など）も連鎖で消える。

### 4.5 選択と構成

- FiniteFreeResolution の `coverRank`・`cover`・`coverπ` は `(Module.Finite.exists_fin' R M).choose…`。構造体 1 つの def か、Mathlib の表示の API に。
- MapExtend は `∃ i, e.f i = i'` の `choose_spec` を 8 回使う。`e.r` か明示の添字に。

### 4.6 提出候補

左導来関手の長完全列（加群圏の間の加法関手）、平坦なら Tor が消える、Tor の零化イデアルの評価、Tor の対称性、`colim` の Additive・Linear、
`mapExtendIso`、`fromLeftDerivedZero` の関手についての自然性、局所平坦性判定、Noether 環上の Tor の有限長・台・有限性、`ModuleSubcomplex`、
DirectedHomology、`FiniteSupportCoproduct`。Auslander–Buchsbaum は上流の PR を追う（出し直さない）。

## 5. HA4 DerivedCompletion の塔の側（88 → 約 15 ファイル）

### 5.1 統合

| 新しいファイル | 元のファイル | BS |
| --- | --- | --- |
| Tower/HolimModel | TowerComplex・TowerIso・ProductHomology・ProductCoordinates・ProductHomotopy・TowerCoordinates・TowerHomology | なし |
| Tower/Maps | TowerUnit（一般の部分）・TowerProjection・TowerMap・TowerIsoProjection・TowerIsoMapCompatibility・TowerLiftNaturality・TowerExact | なし |
| Tower/Milnor | MilnorSequence・TowerHomologyNaturality・MilnorNaturality・MilnorMapZero・MilnorAnnihilator・UniformZeroTower・UniformZeroTowerHomology・ConstantTower | MilnorAnnihilator（2） |
| Koszul/Tower（軽い） | KoszulTower・KoszulCanonicalZero・KoszulStageZero、TowerUnit の `koszulComplexInclusion`・`koszulCompletionUnit` | KoszulCanonicalZero（1） |
| Koszul/Completion | KoszulMilnor・KoszulUnitCompatibility・KoszulStageComplete・TowerComplete・TowerHomologyComplete | TowerComplete（4） |
| Localization | LocalizationPresentation・LocalizationResolution・LocalizationHomCoordinates・LocalizationTowerComparison・ScalarTowerInversion | なし |
| Reflection | ReflectionRing・ReflectionTransport・PrincipalReflectionPresentation・PrincipalReflectionComplete | 名前を使う |
| Principal/KoszulModel | PrincipalTowerPresentation・PrincipalKoszul{Stage,Product,Cone,Unit,Ring}・ScalarRestriction・PrincipalQuotientComplete | あり（`PrincipalCompletionH0` 29 回） |
| Principal/Comparisons | PrincipalCompletionDerivedComparison・PrincipalCompletionFunctor・PrincipalClassicalComparison（PrincipalIdeal は CLMST 専用なので別） | あり |
| Pair/* | Pair{TowerPresentation,TowerEvaluation,TowerUniqueness}・PairKoszul{Stage,Transition,Comparison,Product,Cone,Unit,Ring}・IteratedKoszulRing・PairIterationComparison・PairZeroCompletion | 名前を使う（§5.3） |
| PowerTower | PowerTorsionTower・PowerTorsionComplex・PowerImageTower・PowerCokernel{Reconstruction,Naturality,TensorModel,Transitions}・KoszulPowerCokernelComparison・PowerTowerLimitBound | なし |
| PowerTorsionTor | PowerTorsionTensor・PowerTorsionTorExtension・PowerTorsionTorConormal（Tor と正則局所環を引く。HA3 の Tor 側へ移すのが自然） | PowerTorsionTensor（1） |
| Restriction | RestrictionKoszulStage・RestrictionTower（軽い）と RestrictionComplete・RestrictionCompletionEquivalence・RestrictionCompletion（重い）に分ける | RestrictionCompletion（6） |
| IteratedTensor | IteratedAlgebraH0Comparison・IteratedTensorH0Complete・IteratedTensorQuotientComparison・IteratedTensorCartier{Algebra,LinearComparison,Products} | 使うのは BS/Prism/Tensor/PerfectPrismTensor だけ |

- TowerMap が HA5 の ComplexCompletionQuasiIso を import している。本当に必要か確かめる（不要なら Tower/* は HA5 より下に置ける）。
- IteratedTensor* は BS の PerfectPrismTensor 専用。BS 側へ移すのが自然だが、BS は別セッションの管轄なので、BS 側の作業として申し送る。
- 死んだファイル：PowerTorsionTorProduct。

### 5.2 Mathlib との重なり

- Koszul 複体、holim、Milnor 列、lim¹、導来完備化はどちらの版にもない。`mulLeft_range_eq_span` は `Submodule.span_singleton_eq_range`
  の言い直し（確度高）。`complexProductHomologyEquiv` は `AB4Star (ModuleCat R)` と `HomologicalComplexLimits` から出せる（確度中）。

### 5.3 一本化

- **Pair* を Principal* の反復で置き換える**：PrincipalTowerPresentation ↔ PairTowerPresentation、Principal{Reflection} ↔ PairTower{Evaluation,Uniqueness}、
  PrincipalKoszul{Stage,Product,Cone,Unit,Ring} ↔ PairKoszul{…}、さらに IteratedKoszulRing がファイル単位で並行（Pair 側は約 1900 行）。
  PairIterationComparison が pair ≅ principal の反復を証明済み。`pairKoszulCoordinates`（BS 16 回）・`PairCompletionH0`・`pairCompletionCommRing`
  （6 回）・`pairCompletionUnitRingHom` は名前として残し、定義を反復の側に移す。n 変数への一般化も同時に得られる（一般の `Fin e` の Koszul 塔
  は完備性まではすでに n 変数）。
- `principalCompletion_existsUnique_*`・`pairCompletion_existsUnique_*`・`iteratedCompletion_existsUnique_ringHom` と `*_isModuleComplete_unit_{first,second}`
  はどれも `IsCompleteModuleReflection` の例。一般の補題 1 本にする。
- UniformZeroTower・UniformZeroTowerHomology・PowerTorsionTower・PowerTorsionComplex は同じ仕組み。ConstantTower・ScalarTowerInversion は Milnor の特殊化。
- 自然性の補題（TowerHomologyNaturality・MilnorNaturality・TowerLiftNaturality・TowerIsoMapCompatibility）は 1 節に。

### 5.4 未使用

`completedUnitH0PDEquiv_unit`、`complexCompletion_single_eq_koszul`、`constantComplexTowerUnitIso_inv`、`flat_powerTorsionTowerDifference_bijective`、
`iteratedAlgebraCompletionH0PDAlgEquiv_unit`、`iteratedCompletedTensorCartierH0Iso_left/_right`、`iteratedTensorCartierCompletedAlgEquiv_toAlgHom`、
`koszulPowerCokernelComparison_quasiIso`、`pairKoszulCompletionShortComplexIso_hom_τ₂`、`principalCompletionShortComplexIso_hom_τ₂`、
`scalarComplexTowerHomotopyLimit_smul_isIso`、`tor_eq_zero_of_power_torsion_and_conormal`、`tor_ideal_sq_zero_of_power_torsion_tests`。
ファイルの中だけで使われている名前が約 150（LocalizationResolution 10、PowerCokernelTensorModel 7、PairZeroCompletion 7 など）は private に。
ルート直下の一般的な名前（`shortComplexZero`・`diagonalSequence`・`sequenceDiagonal`・`sequenceShiftRight/Tail/Head`・`isModuleComplete_zero`）も private か名前空間へ。

### 5.5 選択と構成

- 一意存在の定理から `.choose` で写像を作っている：PrincipalCompletionFunctor（L54・66）、PairIterationComparison（L23–55）、PairZeroCompletion（L29・41）、
  PrincipalClassicalComparison（L71）。既にある `IsCompleteModuleReflection.liftAlgHom` を使う。`_comp`・`_unit` の補題が rfl に近くなる。
- ReflectionRing の `surjective` の `.choose` は `Function.surjInv`、PrincipalReflectionComplete の `mkQ_surjective` の `.choose` は `Quotient.out` に。

### 5.6 提出候補

ℕ 塔の holim `mappingCone(1 − shift)⟦-1⟧` と Milnor 列（AB4* のアーベル圏へ一般化して）、AB4* での homology と積の可換、一様零の塔と定数塔の
lim・lim¹、望遠鏡による `R[1/a]` の長さ 1 の自由分解、`IsCompleteModuleReflection` から環構造。導来完備化が上流に入った後に：正則主イデアルの
導来完備化の H⁰ ≅ `AdicCompletion`、完備化と係数の制限の可換。

## 6. HA5 DerivedCompletion の完備化の側（104 → 約 15 ファイル）

### 6.1 統合

| 新しいファイル | 元のファイル | BS |
| --- | --- | --- |
| ModuleComplete/Basic | Basic・Module・AdicComparison・ModuleClosure・ModuleHomComplete・Torsion・FinitePresentationComplete・DivisibleHomZero・Jacobson・BoundedTorsionComparison・CompleteSequenceSum、HA4 の `adicRecurrenceEquiv` | `IsModuleComplete`（35） |
| ModuleTower | ModuleTower・ModuleTowerEquiv（AdicTower は削除） | なし |
| ConeAPI | ConeShortExact・ConeBoundaryNormalization（ModuleConeCoordinates・ModuleConeNaturality は 6 行の再エクスポートなので削除し、importer 4・7 本を付け替える） | なし |
| ComplexCompletion | ComplexCompletion・…QuasiIso・…Derived・…Naturality・…Reconstruction・…HomologyComplete・Closure・TermwiseComplete | あり |
| CompletionReflection | CompletionReduction・DerivedKoszulReduction・ComplexCompletionReflection・CompletionTriangulated・KProjectiveProduct・ModuleResolution | あり |
| BoundedAboveCompletion | BoundedAboveCompletion・…Equivalence・CompletionUpperBound・CompletionH0Comparison・CompletionHomologyDivisibility | あり |
| CompletionMonoidal | CompletionTensorComparison・CompletionTensorCoherence・CompletionAlgebraObjects・CompletionH0Algebra・…Universal・CompletionPointAction（重いので BoundedAboveCompletion と分ける） | あり |
| CompletedTensorVanishing | CompletedTensorZero・CompletedTensorModuleAction・CompletedBaseChangeTriangle・CompletedModuleShortExact・CompletedTensorShortExact | あり |
| CompletionQuotient | CompletionQuotient・CompletionQuotientBaseChange・CompletionScalarConeComparison・RegularTensorReduction | あり |
| CompletedBaseChange | CompletedBaseChangeScalar・CompletedTensorCoefficient・CompletedBaseChangeH0Coefficient・AlgebraBaseChangeTensorUnit | あり |
| CompletedAlgebraH0 | CompletedAlgebra{Restriction,ScalarAction,UnitNormalization,PrincipalComparison,PDComparison}・CompleteFirstPairComparison・CompletionH0PrincipalComparison・CompletedTensor{AugmentationCriterion,PDComparison,H0Comparison,ClassicalComparison,H0RingTransport}・CompletedSurjectiveAlgebraMul（一本の鎖） | あり |
| ModulePower | ModulePower{Reduction,TensorModel,DerivedComparison,TensorHolim,HolimNaturality,TorComparison,TensorTorZero,TorsionBound}・BoundedTermTorsionComparison・FiniteCoefficient{PowerComparison,PowerHolim,CokernelHolim}・FiniteTensorComplete | CLMST |
| TorAlgebraComplete | ModulePowerTorAlgebra{Tower,Almost,Milnor}・TorAlgebraMilnor{Actions,Middle,Sequence}・TorAlgebraComplete | CLMST |
| DerivedPurity | CompleteScalarConePurity・CompleteFlatReductionPure・CompleteFlatReductionBounded・DerivedPowerCokernelModel・CompleteMilnorAnnihilator・RegularCompletionPure・PerfectResidueCompletedTensor | あり（多い） |
| IdealExtension | CompleteIdealExtension・ConormalIdempotentImage・ConormalExtension・TorOneCompleteExtension・CompletedQuotientTensorExtension | あり |

- PDCompletion（BS 33 ファイル）は名前もパスも当面そのまま。HA4 の Pair の置き換えと合わせて扱う。
- 層の注意：ComplexCompletionReconstruction は HA4 の TowerExact・LocalizationTowerComparison を import する。CompletedTensorShortExact は
  ModulePowerDerivedComparison を import する。FinitePresentationComplete は HA4 の ReflectionTransport が要る。
- 死んだファイル：AdicTower（audit_clmst の `assert_no_sorry` だけ。監査の行も消す）、CompletedTensorModuleReduction、FlatResidueLimitTorsion。

### 6.2 Mathlib との重なり

- `adicTowerTransition` は `AdicCompletion.transitionMap`、`adicTowerLimitEquiv` の行き先はすでに `AdicCompletion`（ファイルごと削除）。
- `mem_jacobson_bot_of_isModuleComplete` は `IsAdicComplete.le_jacobson_bot` の導来版（仮定が弱いので重複ではない）。
- `boundedAboveCompletionCommMonFunctor`・CompletionTriangulated は Mathlib の `Functor.mapCommMon`・`ObjectProperty.IsTriangulated` を正しく使っている。
- `coneStandardShortComplex` は `CochainComplex.mappingCone` の API・DegreewiseSplit と一部重なる見込み（確度低〜中）。

### 6.3 一本化

- **PD の d = 0 経由の H⁰ 同型**：`PDCompletionH0 B p 0` は `PairCompletionH0 (p) 0` で、principal の完備化に行くための遠回り。
  `completedTensorH0PDAlgEquiv`・`…OfIso`・`…OfTor`・`…OfKoszul` は型が同じで、一致を示す `…_eq_of*_apply` 3 本は未使用。
  `completedTensorH0AlgEquivOfKoszul` は一般の `a` の版、`completedTensorH0PrincipalRingEquiv`・`…AdicRingEquiv` は d = 0 経由、
  `completedAlgebraH0PDAlgEquiv`・`…PDBAlgEquiv` と `completedAlgebraPrincipalH0AlgEquiv`、`completionH0PrincipalAlgEquiv` と同、
  `completionH0PairAlgEquivOfCompleteFirst` と `pairCompletionPrincipalAlgEquivOfCompleteFirst` が重複。
  → `derivedH0AlgEquivOfIsoHomology` 型の輸送 1 本と、principal と pair(·, 0) をつなぐ補題にまとめ、PD の d = 0 の層をなくす。BS が使う
  `completedTensorH0AdicRingEquiv(_left/_right/_algebraMap)` は名前を残す。
- 複体の水準と導来の水準の並行：`complexCompletionReductionIso/NatIso` と `derivedComplexCompletionReductionIso/NatIso`、
  `derivedComplexCompletionFunctor`（D(R)）と `boundedAboveDerivedCompletionFunctor`（D⁻）。
- 「完備化は、完備性を保つ完全関手と可換」の Comparison・`_unit`・`_isIso`・Iso・`_naturality`・NatIso の型が 3 回（CompletionScalarConeComparison・
  CompletionQuotientBaseChange・CompletionReduction）。一般の補題 1 本に。
- `modulePowerTorAlgebraLimitComparison`・`LimOneComparison`（Tower、未使用）と `modulePowerCokernelTorAlgebraLimitComparison`・`LimOneComparison`（Milnor）。
- `completedAlgebraBaseChangeTensorIso` と `completedBaseChangeTensorH0Iso`。

### 6.4 未使用

`isComplete_Q_of_termwise_pow_smul_zero`、`boundedAboveDerivedCompletionInclusionIso`、`completeComplex_homology_pow_annihilated`、
`completedBaseChangeTriangleIso`、`completedTensorH0AlgEquivOfKoszul_unit/_left/_right`、`completedTensorH0PDAlgEquivOfIso_left/_right`、
`completedTensorH0PDAlgEquiv_eq_of{Iso,Tor,Koszul}_apply`、`completedTensorH0LeftScalarTower`、`completionH0_existsUnique_algHom`、
`completionQuotientBaseChangeNatIso`・`completionScalarConeNatIso`・`complexCompletionReductionNatIso`・`derivedComplexCompletionReductionNatIso`、
`complexCompletionUnitNatTrans`、`derivedComplexCompletion_existsUnique_extension`、`completeReflectorAdjunction_unit`、
`isUnit_one_sub_mul_of_isModuleComplete`、`isModuleComplete_of_natCast_pow_smul_zero`、`isModuleComplete_quotient_span_pow`、
`moduleTowerLimit_flat_residues_power_torsion_bound`、`modulePowerTorAlgebraLimitComparison`・`…LimOneComparison`、
`torAlgebraMilnorShortComplex_restrictIso`、未使用の `*_unit` 補題 9 本ほか。`_apply` には `@[simp]` のものがあるので消す前に確かめる。

### 6.5 選択と構成

- `pairCompletionToPrincipalOfCompleteFirst`・`principalCompletionToPair`（CompleteFirstPairComparison）と `completionH0PrincipalAlgEquiv` の中は
  一意存在の `.choose`。既存の `completionH0AlgebraLift` のような持ち上げの def にし、一意存在は「持ち上げ＋ext」の系にする。
- `adicRecurrenceEquiv` を ModuleComplete/Basic へ下ろす（CompleteSequenceSum がこの 1 定義のために Principal のファイルを import している）。

### 6.6 提出候補

`ModuleTower` の差分写像と極限、`moduleTowerDifference_surjective`、lim¹（加群の Mittag-Leffler 型）、`ideal_mod_power_idempotent_of_conormal_surjective`、
`algHomOfDenseLinearExtension`、`hom_eq_zero_of_scalar_zero`、`isUnit_one_sub_mul_of_recurrence_bijective`、`exists_power_torsion_bound_of_noetherian`・
`flat_tensor_power_torsion_bound`、ConeShortExact（Mathlib になければ）、KProjectiveProduct。長期：導来 I 完備性（`R_f` への Ext の消滅、三角形で閉じる、
正則・有界ねじれでの `IsAdicComplete` との比較、Stacks 091N・091P）。

## 7. 順序の案

BS の再ビルドの量で二層に分ける。

1. **第一層（BS に触れない）**：BS が import しないファイルだけを動かす。死んだファイルの削除、未使用の宣言の削除、Mathlib への置き換え
   （確度高のもの）、HA1 の大部分（Complex/*・Tensor/*・LinearYoneda・ComplexColimits・MinimalResolution）、HA3 の CLMST 側
   （Koszul/ParameterAnnihilators・LocalCohomology/*・Resolution/FiniteFree）、HA4 の Tower/*・Localization・PowerTower、HA5 の ModulePower・
   TorAlgebraComplete（CLMST だけ）。BS が import するファイルの中身は変えない。
2. **第二層（BS の再ビルドを伴う）**：DerivedCompletion の BS 向けのファイルの統合、Pair の置き換え、PD の d = 0 の層の整理、導来テンソルの一本化、
   `.choose` の def 化（BS が使う名前のもの）。CommutativeAlgebra で保留している「BS の再ビルドの一括作業」（Koszul・KoszulResolution の移動、
   BS が import する X 群の 3 本）とまとめて 1 回にする。BS のセッションと時期を合わせる。

第一層の中は HA1 → HA3 → HA2 → HA4 → HA5 の順（import の下から）。各群の中では死んだファイル・未使用の削除を先にし、統合はその後。

## 8. 決定待ち

1. ~~Auslander–Buchsbaum を残すか削除するか~~ → 削除（2026-10-30）。
2. ~~StupidTruncation の置き換え~~ → Mathlib を上げるまで保留（2026-10-30）。
3. ~~Tensor をどちらに寄せるか~~ → 本体は `HomologicalAlgebra/CochainTensor/`（Basic・Symmetric・Shuffle・DegreeMaps・ShortExact・BaseChange・
   Cone/Shift/Single/Acyclic）。PerfectComplex には完全複体などの固有部分だけを残し、殻 21 本は PC2 で削除。`cochainTensor` は名前を残し、
   ほかは Mathlib の記法へ段階的に寄せる（利用の多いものは `@[deprecated] alias`）。PC2 と同時に行う（2026-10-30）。
4. ~~IteratedTensor*~~ → コーディネータが `BhattScholze/Prism/Tensor/` の下へ移す（BhattScholze/ を編集しない決まりの、この件だけの例外。2026-10-30）。
   第二層の作業時間に合わせて行う。
5. ~~第二層の進め方~~ → (a)：BS の作業の区切りに時間を決め、BS 側の編集を止めて第二層をまとめて行い、全体ビルド 1 回でコミットする。
   CA で保留している BS の再ビルドの作業も同じ時間に行う。準備（スクリプト）は第一層の間に済ませる（2026-10-30）。
