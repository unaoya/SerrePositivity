# R-C：仮定入力の一覧（2026-10-24）

R-C 適用後の main の Lean ソースを走査。定義行・import 行を除く一致行数と、その行を含むファイル数を記録する。証拠を供給する定理の行も使用に含む。R17 により HasSpaceLimitsOfShape は任意の形で供給可能。その他の入力の数学的な解消は本リファクタの範囲外。

## IndFiniteLimitExchangeInput

- 定義：`SerrePositivity/InfinityCategories/F2/Ind/FiniteLimitExchangeInput.lean:18`。
- 使用：11／9。

- `SerrePositivity/InfinityCategories/F2/Compact/FiniteColimitClosure.lean:28` `(hκ : Cardinal.aleph0 ≤ κ) (hex : Ind.IndFiniteLimitExchangeInput.{max u v})`
- `SerrePositivity/InfinityCategories/F2/Compact/FiniteColimitClosure.lean:37` `(hκ : Cardinal.aleph0 ≤ κ) (hex : Ind.IndFiniteLimitExchangeInput.{max u v})`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteCoconeSections.lean:31` `(κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteColimitExactness.lean:24` `(hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteColimitExactness.lean:34` `(hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteConeExactness.lean:50` `(hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteIndCommaSections.lean:47` `(κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteYonedaColimitPreservation.lean:22` `(hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteYonedaOppositeLimits.lean:22` `variable (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteYonedaSliceSections.lean:24` `(κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})`
- `SerrePositivity/InfinityCategories/F2/Ind/OppositeUnstraighteningSections.lean:21` `variable (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})`

## CoherentFilteredLimitExchangeShape

- 定義：`SerrePositivity/InfinityCategories/F2/FilteredExchange/CoherentFilteredLimitExchange.lean:24`。
- 使用：9／7。

- `SerrePositivity/InfinityCategories/F2/Compact/ColimitClosureExchange.lean:29` `(hK : CoherentFilteredLimitExchangeShape K.op) : IsKappaCompact.{u, v} κ a.vertex := by`
- `SerrePositivity/InfinityCategories/F2/Compact/ExchangeCoconeCompletion.lean:37` `[Quasicategory B] [IsFilteredInfinity B] (hK : CoherentFilteredLimitExchangeShape K)`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/CoherentFilteredEmptyExchange.lean:24` `CoherentFilteredLimitExchangeShape K := by`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/CoherentFilteredEmptyExchange.lean:48` `CoherentFilteredLimitExchangeShape (⊥ : X.Subcomplex) := by`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/CoherentFilteredExchangeIso.lean:24` `(hK : CoherentFilteredLimitExchangeShape K) : CoherentFilteredLimitExchangeShape L := by`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/CoherentFilteredExchangeIso.lean:42` `CoherentFilteredLimitExchangeShape K ↔ CoherentFilteredLimitExchangeShape L :=`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/CoherentFilteredSimplexExchange.lean:24` `CoherentFilteredLimitExchangeShape (Δ[n] : SSet.{u}) := by`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteConeExactness.lean:28` `(c : JoinCone D) (hc : IsLimitCone c) (hK : CoherentFilteredLimitExchangeShape K)`
- `SerrePositivity/InfinityCategories/F2/Ind/FiniteLimitExchangeInput.lean:19` `exchange (K : SSet.{u}) [K.Finite] : CoherentFilteredLimitExchangeShape K`

## HasSpaceLimitsOfShape

- 定義：`SerrePositivity/InfinityCategories/F2/FilteredExchange/SpaceLimitShapes.lean:25`。
- 使用：7／3。

- `SerrePositivity/InfinityCategories/F1/Yoneda/PresheafSmallLimits.lean:23` `(hB : F2.HasSpaceLimitsOfShape B)`
- `SerrePositivity/InfinityCategories/F1/Yoneda/RepresentablePresheafLimits.lean:36` `(hK : F2.HasSpaceLimitsOfShape K) :`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/SpaceLimitShapes.lean:29` `lemma hasSpaceLimitsOfShape (K : SSet.{u}) : HasSpaceLimitsOfShape K :=`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/SpaceLimitShapes.lean:34` `(hK : HasSpaceLimitsOfShape K) : HasSpaceLimitsOfShape L := by`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/SpaceLimitShapes.lean:49` `HasSpaceLimitsOfShape K := by`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/SpaceLimitShapes.lean:60` `HasSpaceLimitsOfShape (⊥ : X.Subcomplex) := by`
- `SerrePositivity/InfinityCategories/F2/FilteredExchange/SpaceLimitShapes.lean:67` `HasSpaceLimitsOfShape (Δ[n] : SSet.{u}) := by`

## DGKappaConeInput

- 定義：`SerrePositivity/KST/NonConnective/DGKappaConeInput.lean:47`。
- 使用：16／16。

- `SerrePositivity/KST/NonConnective/DGKappaFullPerfAction.lean:33` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaPerfClosedEdges.lean:23` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaPerfZeroFamily.lean:24` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)`
- `SerrePositivity/KST/NonConnective/DGKappaPerfectInput.lean:23` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaSplitInclusions.lean:23` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaSplitNativeSquare.lean:25` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaSplitProjections.lean:23` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaSplitRelations.lean:22` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaSuspension.lean:23` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaSwindle.lean:22` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaSwindleInfinity.lean:27` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaZeroFunctor.lean:24` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGKappaZeroPerfAction.lean:22` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)`
- `SerrePositivity/KST/NonConnective/DGSuspensionIteration.lean:27` `cone : DGKappaConeInput R A κ`
- `SerrePositivity/KST/NonConnective/DGSwindleFixedK.lean:26` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`
- `SerrePositivity/KST/NonConnective/DGSwindleInputIso.lean:26` `{κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)`

## DGKappaPerfectInput

- 定義：`SerrePositivity/KST/NonConnective/DGKappaPerfectInput.lean:36`。
- 使用：3／2。

- `SerrePositivity/KST/NonConnective/DGKappaPerfectInput.lean:49` `def dgKappaPerfectInclusion (P : DGKappaPerfectInput R D I) :`
- `SerrePositivity/KST/NonConnective/DGKappaPerfectInput.lean:55` `lemma dgKappaSuspension_kills_perfect (P : DGKappaPerfectInput R D I)`
- `SerrePositivity/KST/NonConnective/DGSuspensionIteration.lean:29` `perfect : DGKappaPerfectInput R A cone`
