# KTheory の整理計画（2026-10-30）

概要：論文の層の見直しのうち、`SerrePositivity/KTheory/`（151 ファイル、約 13800 行。トップ階層 40、Adams/ 111）について、
ファイルの統合、未使用の宣言の削除、Mathlib への置き換え、重複の一本化、Mathlib への提出候補をまとめる。
群ごとの調査（2026-10-30、読むだけ）の結果を元にした計画で、実作業はまだ行っていない。
方針：作業の決まりは [commutative-algebra-refactor-plan.md](commutative-algebra-refactor-plan.md) の §2 と同じ。
二乗と三乗で並行している議論の一般化は [perfect-complex-refactor-plan.md](perfect-complex-refactor-plan.md) と共有するので、
両方を合わせて決める（§5）。
規約：Mathlib の確認は固定版（2026-10-07）と最新版（2026-10-28）の両方で行い、関係する宣言に差はなかった。
使われ方：作業を再開するときの手順書。

## 1. 群の分け方と外への影響

| 群 | 内容 | ファイル数 |
| --- | --- | --- |
| KT1 | トップ階層：G₀・K₀ の局所化、dévissage、係数の延長、台付き加群、格子、極大台の長さ | 40 |
| KT2 | Adams/ の基礎：weight 分解、Lagrange 射影子、cyclic 2・3、Koszul の明示モデル | 67 |
| KT3 | Adams/ の tensor square・tensor cube | 44 |

- BhattScholze・CLMST は KTheory を import せず、宣言の参照もない（KT2・KT3 で確認）。改名の波及は KTheory の中と
  IntersectionMultiplicity/AdamsVanishing{,Two,Three}、`SerrePositivity.lean`、生成される `scripts/audit/adams.lean` に限られる。
- Adams/ の外向きの公開面は、`cup_enlarge_eq_zero`、`cyclicTwoFamily`、`cyclicThreeFamily`、`CubicCoefficientField`・
  `cubicCoefficientRoot*` のほぼ 4 点。

## 2. KT1 トップ階層（G₀・K₀ の局所化、dévissage、係数、格子、極大台）

規模：40 ファイル、3618 行（最大は G0Localization の 216 行）。主な利用者は KTheory/Adams（約 30 ファイル）、PerfectComplex の 4 本
（IntegerEuler・TensorTorComparison・CoefficientEuler・CubicActionClass が KTheory を import する）、InfinityCategories/Derived/SupportK0、
IntersectionMultiplicity/AdamsVanishing。SupportedModule の下流は 74 モジュール（Paper 13、IntersectionMultiplicity 8 など。BS は含まない）。

### 2.1 統合（40 → 12 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| G0/Basic（約 330 行） | SupportedModule・G0Supported・SupportedExactEuler の `image`・`coimage`・`mk_of_isZero`・CA の SubmoduleExact |
| G0/Functoriality（約 200 行） | G0Functoriality・G0Torsion の `localize_mk_eq_zero` |
| G0/Lattice（約 280 行） | SupportedLattice・LatticeClass・LatticeExact |
| G0/Localization（約 400 行） | G0Torsion・TorsionAnnihilator・G0Localization・LocalizationKernelSupport |
| G0/MaximalSupport（約 380 行） | MaximalSupportModules・MaximalSupportLength・MaximalSupportLocalLength・MaximalSupportLengthEquiv・Adams の MaximalSupportModules・MaximalLengthEvaluation・MaximalLengthEquiv |
| G0/SemilocalSupport（約 330 行） | CA の SupportHeight・SemilocalSupport・ModuleSupportHeight（CA 計画で KTheory に回したものの受け入れ先。Adams の再エクスポート 2 本は削除、SupportHeight の未使用 3 宣言は移動時に削除） |
| Comparison/ResolutionClass（約 200 行） | ResolutionClass・ResolutionAdditivity |
| Comparison/HomologyEuler（軽量） | SupportedExactEuler の Euler 部分・HomologyEulerBasic（PerfectComplex/IntegerEuler が import するので重い比較と分ける） |
| Comparison/Basic（約 470 行） | HomologyEuler・HomologyPeeling・ComparisonInverse・ComparisonNaturality |
| K0Localization | K0Localization |
| Coefficients（軽量） | G0Coefficients・SupportedCoefficients（PerfectComplex の CoefficientEuler・CubicActionClass が import するので軽く保つ） |
| LocalizationCoefficients | LocalizationCoefficients・K0LocalizationCoefficients・MaximalSupportCoefficientLength |

- 削除：再エクスポートの ModuleClosedSupport（4 行。TensorTorComparison は CA の ModuleClosedSupport を直接 import）・LocalizedResolution（10 行）。
  CoefficientExtension・CoefficientExactness・CoefficientLinearExtension は Mathlib に置き換え、残り（`coefficientPairing`）を LinearAlgebra へ。
- dévissage 一式（Devissage* 7 ファイル、654 行）：利用者がいない（`g0QuotientDevissageEquiv`・`G0` はどこからも使われない。
  Paper/Section5/ModuleReduction が使うのは別物の IntersectionMultiplicity/Devissage）。DevissageAnnihilated が不要な
  K0LocalizationCoefficients を import しているので依存グラフの最上段に載っている。論文の層から外す（research/ に退避するか削除）。
- 循環の前提：ComparisonNaturality → LocalizationCoefficients（不要）と DevissageAnnihilated → K0LocalizationCoefficients（偽の依存）の
  import を先に外す。ResolutionClass → G0Localization の LocalizedResolution 経由の依存も偽物。

### 2.2 Mathlib との重なり（固定版と最新版で差なし）

- 確度高：`g0CoefficientMap E f` は定義が `f.toIntLinearMap.baseChange E` そのもの（`_tmul`・`_comp`・`_id` は `LinearMap.baseChange_tmul`・
  `_comp`・`_id`）。`coefficientLinearExtension E f` → `f.toIntLinearMap.liftBaseChange E`、`coefficientLinearMap_ext` →
  `LinearMap.liftBaseChangeEquiv` の単射性。`idealAnnihilatorTorsion` → `Module.isTorsionBySet_iff_subset_annihilator`。
  `annihilator_le_of_injective`・`_surjective` → Mathlib の `LinearMap.annihilator_le_of_*`。`LinearMap.exact_iff.mpr (by rw [ker_mkQ, range_subtype])`
  の 3 箇所 → `LinearMap.exact_subtype_mkQ`。`localizedModuleTensorEquiv` → `LocalizedModule.equivTensorProduct`（未使用なので削除）。
  `coefficientField_flat` は `inferInstance` だけなので削除。
- 確度中：`moduleSupport_extendScalars` → `Module.support_subset_preimage_comap`。`g0CoefficientMap_ker_eq_range` は `lTensor_exact` の包み。
  `maximalSupportLengthMap` の加法性 → `Module.length_eq_add_of_exact`。
- Mathlib にないもの：完全列による K₀（G₀）。Mathlib の Grothendieck 群はモノイドの群完備化だけ。使える基盤は `ObjectProperty.IsSerreClass`、
  `IsFiniteLength`、`IsLocalizedModule`、Serre 商の局所化。
- CA 計画で `IsModuleSTorsion` を `Module.IsTorsion'` に置き換えると、G0Torsion・TorsionAnnihilator・LatticeClass・G0Localization・
  LocalizationKernelSupport が波及を受ける。

### 2.3 一本化

- 局所化完全列が G0・K0 × ℤ・係数 E の 2×2 に 3 版を加えた形で重複（`localize_surjective`・`localize_kernel_supported`・
  `localize_enlarge_principal_eq_zero`・`localize_away_kernel_range`）。閉台の族に `enlarge` と `localize` を持たせた構造と、
  「自然同型に沿って核と右完全性を移す」「核が `enlarge` の像の有向合併という性質は `baseChange E` で保たれる」の 2 つの汎用補題を置けば、
  K0 版と係数版は系になる（約 200 行減）。
- `enlarge` 版と `map` 版の自然性が二重（`resClass_*`・`resolutionMap_*`・`homologyEuler_*`）。逆写像に沿って可換図式を移す補題一つか、
  `enlarge` を `map (RingHom.id)` の特殊例にする。
- 係数版の定義（G0 と K0 の `coefficientEnlarge`・`coefficientLocalize`・`coefficientMap` など）はすべて `baseChange` の別名。Adams が
  多用する（`Coefficients` 57 箇所、`coefficientEnlarge` 24 箇所）ので名前は `abbrev` で残し、別名と補題は Mathlib に寄せる。
- Euler 加法性が CategoryTheory と二重実装（`SupportedExactEuler.mk_exact_images` ↔ `ExactSequenceEuler.additiveLength_exact_images`、
  `supportedHomologyEuler_*` ↔ `HomologicalEuler.homologicalEuler_*`、`K0WithSupport.homologyEuler` ↔ `homologicalEulerK0`）。値域を任意の
  `AddCommGroup` にし、評価を `IsSerreClass` な部分圏上の関数とした `homologicalEulerK0` 一本にすれば、G0 版はその普遍例、ℝ 版と
  IntegerEuler はその合成になる。
- 部分加群・商の短完全列を 6 回、制限の短完全列を 2 回組み立てている → `SupportedModuleShortExact.ofSubmodule`・`restrict` の一般の def に。
- 「台 ⊆ V(J) から annihilator の冪を得る」が 5 箇所 → CA に「有限加群で Module.support ⊆ V(J) ↔ J ≤ √ann、∃ n, J^n ≤ ann」を置く。
- `HasPrincipalLocalizationSupport` と `HasPrincipalCoefficientSupport` は同じ述語。CA/PrincipalSupport の隣に一本化。
- `K0WithSupport.localize` の第 1 引数は未使用。K0Localization の `[IsNoetherianRing S] [HasFiniteProjectiveResolutions S]` は局所化から
  導けるので、主補題から外せば `_of_resolution_contract` の 3 版が消える（Adams が使うのは 1 つだけ）。

### 2.4 未使用

- dévissage 一式（§2.1）。
- 個別：`coefficientLinearExtension_unique`、`k0Class_eq_sum_resolutionClasses`、`PerfectModuleResolution.exists_homotopyEquiv`
  （PerfectComplex 側に置けば使い道あり）、`directSum`・`directSumShortExact`・`mk_directSum`（`@[simp]`）、`G0WithSupport.mk_zero`（`@[simp]`）、
  `finiteModuleSupportedOn.top_iff`、`supportedFGModuleOnObj`、`localizedModuleTensorEquiv`、`coefficientField_flat`、
  `coefficientLocalize_ker_range`、`coefficientTorsionInclusion_injective`、`eq_sum_localLengthMap`、`coefficientCup_enlarge`・
  `coefficientCup_map`（基底変換との両立として残す価値あり）、`localize_surjective_of_resolution_contract`、
  `localize_kernel_supported_of_resolution_contract`、`G0WithSupport.enlarge_map`。
- 内部だけで使うもの（private 化）：`principalLocalizationSupportSubgroup`、`exists_supported_lattice`、`coefficientEnlarge_refl`、
  `mk_complex_shift`。instance `sourceLocalizationMap_isLocalizedModule` は暗黙に使われているので残す。

### 2.5 外へ回すもの

- PerfectComplex へ：`PerfectModuleResolution` 本体と `augmentation`・`exists_comparison`・`comparison_quasiIso`・`support`・`baseChange`・
  `mappingCone`、`hasFiniteProjectiveResolutions_of_localization`、`K0WithSupport.mk_shift`・`mk_complex_shift`（`K0WithSupport` は
  PerfectComplex/ClosedSupportK0 で定義）。逆向きに PerfectComplex の計画は IntegerEuler 系・Adams の Koszul・FiniteProjectiveResolutions を
  KTheory へ回す（perfect-complex-refactor-plan §2.1）。どちらを KTheory の上の層とするかは二つの計画で合わせて決める。
- HomologicalAlgebra へ：`exists_topHomologyMap`。
- CommutativeAlgebra（Support）へ：`moduleSupport_extendScalars`、`exists_pow_annihilator_of_support`（局所化版も）、
  `moduleSTorsion_of_support_principal`、`quotientModule_annihilator`、`maximalSupport_pullback_le`。
- CategoryTheory へ：Euler の汎用部分。LinearAlgebra へ：`coefficientPairing`・`integerPairing`（引数の型が異なる双線形写像の基底変換）。

### 2.6 提出候補

- 拡大で閉じた ObjectProperty（小さいアーベル圏）の完全列 K₀ と API（`mk`・`lift`・`hom_ext`・`mk_shortExact`、Euler 加法性、完全関手の誘導写像）。
  `G0WithSupport Z` はその特殊例。`finiteModuleSupportedOn Z` の `IsSerreClass` インスタンス。
- 一般形の dévissage、有限長の加群の K₀ は単純加群の同型類上の自由群、K₀ の局所化完全列（Mathlib の SerreClass/Localization と接続）。
- `ModuleCat (R⧸J) ≌ {M | J ≤ ann M}`、`LinearMap.baseChange₂`、台の小さな補題。

### 2.7 リスク

- BS/CLMST への波及はない。
- 監査：`scripts/audit_euler_group_shared.lean`（`G0WithSupport.mk_exact_images`・`supportedModuleEuler_exact_sequence`・
  `supportedHomologyEuler_triangle`）、`scripts/audit_triangulated_k0_shift_shared.lean`（ResolutionClass と `K0WithSupport.mk_shift`）を手で直す。
- Comparison/HomologyEuler を重い比較と統合すると PerfectComplex/IntegerEuler の閉包が 49 から約 110 に増えるので分ける。

## 3. KT2 Adams の基礎

規模：67 ファイル、5909 行。weight 層（約 900 行）、cyclic 2（約 700 行）、cyclic 3（約 450 行）、Koszul の明示モデル（約 3800 行、
うち KoszulCube* が 19 ファイル約 2650 行）。

### 3.1 統合（67 → 10 ファイル、KTheory/Adams/ のまま）

| 新しいファイル | 元のファイル |
| --- | --- |
| Weight（約 300 行） | WeightPolynomial・LagrangeProjectors・WeightOperators・PolynomialNaturality・WeightProduct |
| Family（約 100 行） | Family |
| PureWeight（約 600 行） | IteratedPrimeLocalization・MaximalPureWeight・CoefficientLengthEquiv・MaximalLengthEquiv・MaximalSupportModules・SemilocalPureWeight・WeightDefectLift・WeightAnnihilation・WeightDecomposition・CupVanishing |
| CyclicTwo（約 450 行） | CyclicTwo・SupportNaturality・BaseChangeNaturality・UnitNormalization・KoszulNormalization・CyclicTwoFamily |
| CyclicThree（約 450 行） | CyclicThree・CubicSupportNaturality・CubicBaseChangeNaturality・CubicUnitNormalization・CubicKoszulNormalization・CyclicThreeFamily・CubicCoefficientField |
| KoszulSquare（約 600 行） | KoszulSquareModel・KoszulSquareSwap・KoszulSquareCoordinates・KoszulSquareDual・KoszulShiftOneModel |
| KoszulSquareSplitting（約 570 行、一本化で約 300 行） | Koszul{Positive,Negative}{Embedding,Retraction} |
| KoszulCube（約 950 行） | KoszulCubeModel・KoszulCubeGenerators・KoszulCubeDifferential・KoszulCubeExt・KoszulCubeCoordinates |
| KoszulCubeFourier（約 1000 行） | KoszulCubeFourier{One,OneInverse,OneCoordinates,Two,TwoInverse,TwoCoordinates,Basis（hom_ext のみ）,Embeddings}・KoszulShiftTwoModel |
| KoszulCubeFourierModel（約 500 行） | KoszulCubeFourierModel{Map,Generators,Inverse,Iso,Class} |

- 削除するファイル：互換用に import だけをまとめた 7 本（SemilocalSupport・SupportHeight・KoszulOneBasis・KoszulOneModel・KoszulTensor・
  MaximalLengthEvaluation・Coefficients。importer は実体を直接 import する）、KoszulCubeBasis（全体が未使用）、KoszulShiftTwoClass
  （§3.2 の置き換えで消える）、KoszulSequenceNormalization（全体が未使用）。
- import の向きはほぼ一列（Weight → Family → PureWeight、CyclicTwo・CyclicThree ← KoszulSquare*・KoszulCube*）。KT3 との境界
  （KoszulSquareModel → TensorSquare、KoszulPositiveEmbedding → TensorSquareEigenspaces、BaseChangeNaturality →
  TensorSquareBaseChangeEigenspaces、CyclicThree → TensorCube*）は KT3 と同時に縮約して閉路を確かめる。
- KoszulCube* は `simp` の多い長い証明が集まるので、1 ファイルにせず 3 分割にしておく。

### 3.2 Mathlib との重なり

- 確度高：`polynomial_on_eigenvector` = `Module.End.aeval_apply_of_mem_apply_eq_smul`（LinearAlgebra/Eigenspace/Minpoly.lean）。
  `endomorphism_pow_intertwine` → `Module.End.commute_pow_left_of_commute`。`coefficient_empty_zero` はプロジェクト内の
  `K0WithSupport.coefficient_eq_zero_of_empty_support` の包み。`oneKoszulShiftTwo_class` は `TriangulatedK0.mk_shift`（または
  `K0WithSupport.mk_shift`）と `oneKoszulClass` から出る。`oneKoszulShiftOne_class` は `oneKoszulClass_shift_one` の別名。
- 確度中：`cubicCoefficientRoot` は `.choose` で定義されている。`IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)` と
  `zeta_spec` で def と補題に直す。
- Mathlib にないもの：Lagrange 射影子（Mathlib の固有分解は有限次元が前提）、`polynomial_intertwine`、Koszul 複体。

### 3.3 一本化

- `cyclicTwo_koszul`（ℤ 版）は Family の一般補題 `SupportedAdams.koszul` の特殊例で未使用。`coefficientCyclicTwo_koszul`・
  `cyclicThree_koszul` も不要。
- Positive・Negative の 4 ファイルは、符号 ±、次数の位置、相手（`oneKoszulComplex (2a)` か `oneKoszulShiftOne a`）だけが違い、
  証明の骨格は同じ。符号 ε ∈ {±1} で添字付けた一本の補題にする。
- ShiftOneModel・ShiftTwoModel を `oneKoszulShift k` 一本に。
- KoszulCube の Fourier 側の 1 と 2 は、Coordinates・Inverse・Basis の 3 段で 9 項ずつの同じ手計算を繰り返している。
  PerfectComplex/CubicFourierTransform の行列 F と F⁻¹ = (1/3)F̄ を一度示し、「Fin 3 添字の biproduct ≅ Fin 3 → R」に通せば、
  約 500 行の座標補題が `Matrix` の計算に縮む。
- cyclic 2 と cyclic 3 の 6 対（SupportNaturality・BaseChangeNaturality・UnitNormalization・KoszulNormalization・Family・
  `algebraInvertible{Two,Three}`）は「代表元の水準の類が enlarge・map と可換なら `K0WithSupport.lift` も可換」の一本の補題で、
  各 10 行程度になる。`algebraInvertible{Two,Three}` は `Invertible (n : A)` の一般形に。
- `LagrangeProjectors` を「E 代数の元 T で ∏(T − v j) = 0 となるもの」に一般化する（証明はそのまま通る）。そうすれば PerfectComplex の
  `CochainInvolution.positiveMap`（(1+τ)/2）と `CochainCubicAction.projectorMap` が A = End(K) の場合として同じ補題から出る。

### 3.4 未使用

- 確実に削除してよいもの：KoszulCubeBasis 全体（117 行）、KoszulCubeModel の `oneKoszulCubeX{Zero,NegOne,NegTwo,NegThree}Iso` と
  それだけが使う錐の同型 4 つ、KoszulCubeFourierBasis の `{One,Two,Top}BasisIso`（約 115 行、`_hom_ext` 3 本は残す）、
  KoszulSequenceNormalization 全体、`cyclicTwo_unique`、`cyclicThreeValue_unique`、`cyclicThree_unique`、
  `cyclicThreeValue_mk_concrete`、`cyclicThree_koszul`、`coefficientCyclicTwo_koszul`、`iteratedPrimeLocalizationEquiv`、
  `HeightAtLeast.semilocalLengthEquiv`、`HeightAtLeast.localized_module_finiteLength`、`weightPolynomial_top`、
  `SupportedAdams.weightProjector_enlarge`、`LocalizationAdamsFamily.weightProjector_idem`・`_orthogonal`（論文の weight 分解の
  完全な主張として残す選択肢あり）、`oneKoszul{Positive,Negative}Iso_hom_inclusion`、`oneKoszulTensorScalar_unitor`、
  `oneKoszulCubeGenerator_apply`、`cubicCoefficientRoot_primitive`。
- 残すもの：KoszulCubeFourier{One,Two}Coordinates の `@[simp]` 座標補題 18 本（`simp [ht]` が使う）、KoszulSquareDual の `@[simp]` 7 本
  （削除前にビルドで確認）、instance として使われる `oneKoszulCubeFourierModelMap_{f_,}isIso`。

### 3.5 外へ回すもの

- CommutativeAlgebra へ：`iteratedPrime_regular_dimension`、`HeightAtLeast.*`。
- PerfectComplex の Koszul へ：`oneKoszulShift{One,Two}` の一般化、`scalarTensorDiagonal_*`、`scalarModule_braiding_id`、
  `tensorSquareUnit_swap`、`oneKoszulX{Zero,NegOne}_generator_d_apply`。
- KTheory/Coefficient* へ：`coefficientK0LengthEquiv`、`coefficient_eq_zero_of_localizations`（Adams に依存しない）。

### 3.6 提出候補

- Lagrange 射影子一式（有限次元を仮定しない。Mathlib/LinearAlgebra/Lagrange.lean か Eigenspace/）。
- `polynomial_intertwine`（`Module.End.aeval_comp_of_comp_eq` のような名前で）。
- 無限次元の固有分解 `weightDecomposition` の抽象部分。
- 長期的には Koszul 複体（K(a) と、その n 重テンソル ≅ K(a,…,a)）。

## 4. KT3 tensor square・tensor cube

規模：44 ファイル、4235 行（TensorSquare* 15 本 1377 行、TensorCube* 29 本 2858 行）。`maxHeartbeats` の引き上げが cube 側に 18 箇所
（Exact・QuotientAction・HighMixedKernel に集中）。群の外の利用者は Adams/ の中だけ。

### 4.1 統合（44 → 8 ファイル、3 ファイル削除）

| 新しいファイル | 元のファイル |
| --- | --- |
| TensorSquare（約 330 行） | TensorSquare・TensorSquareEigenspaces・TensorSquareMaps・TensorSquareBaseChange・TensorSquareBaseChangeEigenspaces・TensorSquareShuffle |
| TensorSquareFiltration（約 560 行） | TensorSquareFiltration・TensorSquareMixed・TensorSquareMixedSplitting・TensorSquareMixedCancellation |
| TensorSquareClass（約 230 行） | TensorSquareAdditivity・TensorSquareAcyclicClass・TensorSquareEvaluation・TensorSquareMultiplicativity |
| TensorCube（約 230 行） | TensorCube・TensorCubeEigenspaces（未使用分を除く）・TensorCubeMaps・TensorCubeBaseChangeEigenspaces・TensorCubeTensor |
| TensorCubeFiltration（約 500 行） | TensorCubeFiltration・TensorCubeFirstLayer・TensorCubeFirstLayerSplitting・TensorCubeSparsePartition |
| TensorCubeLowMixed（約 850 行、「成分と短完全性」と「回転と台」の二つに分けるのが安全） | LowMixed・LowMixedInclusions・LowMixedSections・LowMixedRotation・LowMixedReconstruction・LowMixedExact・LowMixedSupport |
| TensorCubeHighMixed（約 580 行） | HighMixed・HighMixedComponents・HighMixedSections・HighMixedEpi・HighMixedKernel・HighMixedQuotient（cokernel の部分を除く） |
| TensorCubeClass（約 300 行） | TensorCubeMixedCancellation・TensorCubeAdditivity・TensorCubeEvaluation・TensorCubeMultiplicativity |

- ファイルごと削除：TensorCube{Low,High}MixedQuotientAction、TensorSquareFiltrationImages（中身がすべて未使用）。
- 置き場所は `KTheory/Adams/TensorPower/` にまとめてもよい。import の向きは square が A → B → C、cube が D → E → {F,G} → H。
- `cyclicTwo_cup`・`cyclicThree_cup` は CyclicTwo・CyclicThree を import しているので、C・H に入れると循環する。CyclicTwo.lean・
  CyclicThree.lean へ移す（両者は「生成元 mk X, mk Q 上で cup と可換なら全体で可換」という K0WithSupport の一般補題にまとまる）。
- TensorCubeUnitRotation は CubicUnitNormalization へ。
- 変えない名前（群の外から参照）：tensorSquare(Swap/Map)、`ιTensorObj_tensorSquareSwap`、`tensorSquareClass`、
  `tensorSquare{Positive,Negative}(Projector,_map,_perfect,_support)`、`{Positive,Negative}BaseChangeIso`、
  `tensorSquareEvaluation(_iso,_triangle)`、`cyclicTwo_cup`、`tensorCube(Rotation,_perfect,_support,_apply_ι)`、`tensorCubeAction`、
  `tensorCubeClass`、`tensorCubeCharacterBaseChangeIso`、`tensorCubeEvaluation(_iso,_triangle)`、`cyclicThree_cup`、
  `tensorCubeUnit_rotation`、`tensorCubeUnitIso`。

### 4.2 Mathlib との重なり

- `kernel.map` で置き換えられる（確度高）：`tensorSquareKernelSwap`、`tensorCubeKernelRotation`、`tensorCubeFirstLayerRotation`
  （同変な写像の核へ作用を制限する `kernel.lift` を手で書いたもの）。`_inclusion`・`_sq`・`_cube`・`*_FirstMap_rotation` は
  `kernel.lift_map`・`kernel.map_ι` 系にまとまる。
- `cochainBiprodX_hom_ext`・`cochainBiprodFstX`・`SndX`（TensorSquareMixedSplitting）は HomologicalAlgebra/CochainKernelLift の
  `cochainBiprodDegree_hom_ext` と同じ。どちらも Mathlib の `HomologicalComplex.biprodXIso` と `biprod.hom_ext` で書ける（確度中）。
- `tensorSquareMixedCokernelIso` は CategoryTheory/ShortExactCokernel の `shortExactCokernelIso` と同じだが、未使用なので削除。
- Mathlib にないもの：HomologicalComplex の braided・symmetric 構造、位数 n の作用による指標の射影子分解（`Action V G`、
  `Representation.averageMap`、`IsIdempotentComplete (HomologicalComplex C c)` はある）。

### 4.3 一本化

- Evaluation の 2 ファイルは同じ形。square 側の擬同型不変性を正・負の像ごとに手で示しているのをやめ、PerfectComplex に
  `CochainInvolution.k0Class_eq_of_quasiIso` を足せば TensorSquareMaps はほぼ消える。さらに「擬同型で不変で短完全列に加法的な類関数から
  評価を作る」一般構成を一つ置けば、両方の Evaluation が数行になる（BaseChangeNaturality・SupportNaturality の代表元の取り回しも同じ）。
- `tensorSquareMap_{epi,mono}_of_shortExact` と cube 版は「各次数が射影的なら q^{⊗n} も epi（f^{⊗n} も mono）」の一般補題一本から。
- Splitting の組み立て（square の MixedSplitting と cube の LowMixedExact）は、値域が k 成分の biproduct のときの一般補題に。
- 短完全性の示し方が三通り（square と cube low は各次数の分裂、cube high は epi と核の同定）。high も分裂に揃えると HighMixedKernel
  （約 110 行）が要らなくなる見込み（確度中）。
- 0/1/2 の成分の三重化（HighMixed・LowMixed・Projection・Section・component の 0/1/2）：入れ子の ⊞ を `⨁ j : Fin 3` にし、成分 j を
  成分 0 を rotation^j で輸送したものと定義すれば、j について一度だけ書ける（Sections・Inclusions・Epi で約 700 行の半分以上が減る）。

### 4.4 未使用

- ファイルごと：TensorCube{Low,High}MixedQuotientAction（これで `{Low,High}MixedCokernelIso(_π_hom)`・`tensorCubeHighMixedCokernel`
  も使われなくなる）、TensorSquareFiltrationImages。
- square 側：`tensorSquareClass_eq_zero_of_acyclic`、`{Positive,Negative}BaseChangeIso_hom_inclusion`、`tensorSquareDecompositionIso`、
  `tensorSquare{Positive,Negative}_inclusion_swap`、`tensorSquareEvaluation_concrete`、`tensorSquareClass_shift_one`・`_cone`、
  `tensorSquareKernelFirstMap_mono`、`tensorSquare{Positive,Negative}Map_homotopyEquivalence`、`tensorSquareKernelFirstMap_mixedLeft`・
  `Right`（`@[simp]`）、`tensorSquareMixedPositiveNegativeIso`、`tensorSquareMixedCokernelIso(_π_hom)`、
  `tensorSquareDiagonal{Involution,_perfect,_support}`、`tensorSquare{Positive,Negative}FourIso`。
- cube 側：`tensorCubeDecompositionIso`、`tensorCubeEigenspace_support`・`_inclusion_rotation`、`tensorCubeEigenspaceMap_id`・`_comp`・
  `_homotopyEquivalence`（これで `tensorCubeEigenspaceMap`・`_quasiIso`・`tensorCubeProjector_naturality`・`tensorCubeEigenspace(_perfect)`
  も不要。cube の類は `tensorCubeAction` の `weightedK0Class` だけで済んでいる）、`tensorCubeClass_eq_zero_of_acyclic`、
  `tensorCubeEvaluation_concrete`・`shift_one`・`cone`、`tensorCubeKernelFirstMap_mono`・`_rotation`、`FirstLayerToKernel_mono`
  （instance）、`FirstLayerFirstMap_mono`・`_toKernel`、`tensorCubeLowMixedMap_epi`、`tensorCubeHighMixedSection{0,1,2}X_inclusion`。
- 再利用の価値：square の固有分解 API（Koszul 側で使う可能性）、`*_shift_one`・`*_cone`（論文の記述に対応、一般の評価構成の補題として）、
  `tensorSquareKernelInclusion_range`。
- 削除に伴い利用者がいなくなる：PerfectComplex/CubicActionTransport、CategoryTheory/CubicConjugation、CategoryTheory/ShortExactCokernel。

### 4.5 提出候補

- HomologicalComplex の Koszul 符号付き symmetric monoidal 構造（PerfectComplex 計画の §3.5 と同じ）。
- 前加法的・R 線形・冪等完備な圏で τⁿ = 1、n 可逆、1 の原始 n 乗根があるときの指標の射影子分解（`Action C (Multiplicative (ZMod n))` の上に）。
- 小物：HomologicalComplex の biproduct の各次数の hom_ext、「q が epi で各次数が射影的なら q ⊗ q も epi」。

### 4.6 リスク

- `*_cup` を C・H に入れると循環。それ以外の縮約では閉路はない。
- F・G・H は重い（Additivity は 1.2M heartbeats）。統合すると再ビルドがまとめて重くなる。
- `set_option backward.defeqAttrib.useBackward true` は cube 側だけ。ファイルの先頭に一律で置くと square 側の挙動が変わりうるので
  section 単位で保つ。

## 5. 二乗と三乗の一般化（KT2・KT3・PerfectComplex の PC2・PC3 で共通）

調査の四つの報告が独立に同じ構造を指摘した。

- (a) 作用の型が 2 本ある：`CochainInvolution`（τ² = 1、射影子 (1±τ)/2、類 [P₊] − [P₋]）と `CochainCubicAction`（τ³ = 1、
  射影子 (1/3)Σ a^{−k}τ^k、類 Σ ζ^j ⊗ [P_j]）。前者は後者の p = 2、t = −1、ζ = −1 の場合。一般形は `CochainCyclicAction n`
  （τⁿ = 1、n 可逆、1 の原始 n 乗根 t）、射影子 e_j = (1/n)Σ t^{−jk}τ^k（§3.3 の Lagrange 補題を End(K) に適用）、
  類 `weightedK0Class E ζ = Σ ζ^j ⊗ [im e_j]`。注意：`tensorSquareClass` は K0WithSupport に値を持ち、Coefficients ℤ（ℤ ⊗ K0）とは
  定義上等しくないので、square 側の利用者 6 ファイルのために `ℤ ⊗ K0 ≃ K0` で包む定義を残す。
- (b) 二乗と三乗の層が 1 対 1 に並行（本体、naturality、perfect・support、擬同型、底変換と固有空間、テンソル、Additivity・Evaluation・
  Multiplicativity、cyclic の 6 対）。一般形は `tensorPow n P` と巡回生成元 `rotation n P`。ただし rotation^n = 1 と shuffle との可換性は
  n ごとの符号計算が要り、一般の n では重い。n ∈ {2,3} に限り「rotation、rotation^n = 1、naturality、テンソル同変性」の 4 つの入力から
  残りを出す構造体（例 `CyclicTensorPowerData n`）を作るのが現実的。PerfectComplex 側で「X ↦ X^{⊗n} は対称モノイダル関手で μ は Sₙ 同変」
  という一般論を一度書けば、符号計算もその具体化になる。
- (c) 核・余核への作用の制限が 5 回手で書かれている → `kernel.map`・`cokernel.map` と「同変な写像の核に作用が降りる」補題一本。
- (d) 混合成分の打ち消し（square の A⊗D ⊞ D⊗A、cube の cyclic sum）は「誘導表現では全固有空間が同型なので Σ ζ^j = 0 から類が 0」と
  いう同じ事実。`cochainCyclicSum n (X_0..X_{n−1})` と `weightedK0Class = 0` を一度だけ示す。PerfectComplex の TensorTripleCyclicSum も
  同じ。
- (e) Koszul の明示モデル（約 3800 行）は K(a)^{⊗n} ≅ K(a) ⊗ Λ^•(H)（H は和が 0 の超平面、n 可逆）の n = 2、3 の場合。
  一般形は「基底変換 K(f) ≅ K(f∘g)」と「K(f₁ ⊕ f₂) ≅ K(f₁) ⊗ K(f₂)」を一般に示し、Fourier 行列で H を対角化する 2 段。
  素数 p では weightedK0Class が p[K(a)] になる（Atiyah の巡回冪の計算）。これで 25 ファイル超が一系統になる。
- (f) フィルトレーション全体の一般の n は部分集合の添字と符号で重く、論文に要るのは n = 2、3 だけなので記録だけにとどめる。

費用対効果の見立て：(a)〜(e) の全面一般化は KT2・KT3・PerfectComplex の Involution*・CubicAction*・TensorTriple* をすべて巻き込む大工事。
短期にはすぐ効くものから行う：§3.3 の Positive・Negative の ε による一本化と Shift k の一般化、Lagrange 射影子の共通化、Fourier 座標の
行列化、§4.2 の `kernel.map`、§4.3 の成分の `Fin 3` 化、§3.4・§4.4 の削除（KT2 で約 1500 行、KT3 で 1000 行超の削減見込み）。
全面一般化（(a)・(d)・(e)）は PerfectComplex の PC3 の結果と合わせて判断する。

## 6. 順序の案

PerfectComplex との層の境界は [perfect-complex-refactor-plan.md](perfect-complex-refactor-plan.md) の §5.1 で合わせて決める
（PerfectComplex を下の層にし、`PerfectModuleResolution`・`K0WithSupport.mk_shift` を PerfectComplex へ、PerfectComplex の IntegerEuler 系・
Adams の Koszul・FiniteProjectiveResolutions を KTheory へ）。KTheory 単体の順序：

1. 削除だけで済むもの：KT1 の再エクスポート 2 本と dévissage 一式（論文の層から外す判断が要る）、KT2 の互換 7 本と未使用ファイル 3 本、
   KT3 の未使用ファイル 3 本と §3.4・§4.4 の未使用。BS/CLMST の再ビルドは起きない。
2. Mathlib への置き換え：KT1 の `baseChange`・`liftBaseChange`・`exact_subtype_mkQ` など、KT2 の `aeval_apply_of_mem_apply_eq_smul`・
   `commute_pow_left_of_commute`・`cubicCoefficientRoot` の def 化、KT3 の `kernel.map`。
3. 群内の一本化：KT1 の局所化完全列と Euler 加法性、KT2 の Positive・Negative の ε 化と Shift k と Fourier 座標の行列化と cyclic 2・3 の
   naturality の共通補題、KT3 の Evaluation の一般構成と成分の `Fin 3` 化。
4. ファイルの統合（KT1 → 12 本、KT2 → 10 本、KT3 → 8 本）。KT2・KT3 の境界の import は同時に縮約して閉路を確かめる。
5. §5 の位数 n の作用・n 重テンソル・Koszul の一般化（PerfectComplex の PC3 §4.5 と同時）。最も大きい工事なので、1〜4 の後に費用対効果を
   見て判断する。
