# R レーン：仮定入力の grep 一覧（2026-10-23）

作業ツリーを走査（未追跡も含む）。使用数の定義と供給元は [R 計画 §6](stage-i/refactoring-infinity.md#6-仮定入力の一覧完成後に外す) を参照。
この一覧は採取時点の位置を記録する。数学的内容は変更しない。

```text
SerrePositivity/InfinityCategories/F1/RepresentablePresheafLimits.lean:36:    (hK : F2.HasSpaceLimitsOfShape K) :
SerrePositivity/InfinityCategories/F1/PresheafSmallLimits.lean:23:  (hB : F2.HasSpaceLimitsOfShape B)
SerrePositivity/InfinityCategories/Derived/DGKappaProjectiveComparison.lean:4:public import SerrePositivity.KST.NonConnective.DGKappaConeInput
SerrePositivity/InfinityCategories/F2/CoherentFilteredEmptyExchange.lean:24:    CoherentFilteredLimitExchangeShape K := by
SerrePositivity/InfinityCategories/F2/CoherentFilteredEmptyExchange.lean:48:    CoherentFilteredLimitExchangeShape (⊥ : X.Subcomplex) := by
SerrePositivity/KST/NonConnective/DGSuspensionIteration.lean:3:public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
SerrePositivity/KST/NonConnective/DGSuspensionIteration.lean:27:  cone : DGKappaConeInput R A κ
SerrePositivity/KST/NonConnective/DGSuspensionIteration.lean:29:  perfect : DGKappaPerfectInput R A cone
SerrePositivity/KST/NonConnective/DGSwindleFixedK.lean:26:  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
SerrePositivity/KST/NonConnective/DGKappaSwindle.lean:22:  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
SerrePositivity/KST/NonConnective/DGSwindleInputIso.lean:26:  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
SerrePositivity/KST/NonConnective/DGKappaPerfectInput.lean:23:  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
SerrePositivity/KST/NonConnective/DGKappaPerfectInput.lean:36:structure DGKappaPerfectInput where
SerrePositivity/KST/NonConnective/DGKappaPerfectInput.lean:49:def dgKappaPerfectInclusion (P : DGKappaPerfectInput R D I) :
SerrePositivity/KST/NonConnective/DGKappaPerfectInput.lean:55:lemma dgKappaSuspension_kills_perfect (P : DGKappaPerfectInput R D I)
SerrePositivity/KST/NonConnective/DGKappaSwindleInfinity.lean:27:  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
SerrePositivity/KST/NonConnective/DGKappaSuspension.lean:3:public import SerrePositivity.KST.NonConnective.DGKappaConeInput
SerrePositivity/KST/NonConnective/DGKappaSuspension.lean:23:  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
SerrePositivity/KST/NonConnective/DGKappaConeInput.lean:47:structure DGKappaConeInput (κ : Cardinal.{u}) where
SerrePositivity/InfinityCategories/F2/CoherentFilteredLimitExchange.lean:24:def CoherentFilteredLimitExchangeShape (K : SSet.{u}) : Prop :=
SerrePositivity/InfinityCategories/F2/Compact/ExchangeCoconeCompletion.lean:37:    [Quasicategory B] [IsFilteredInfinity B] (hK : CoherentFilteredLimitExchangeShape K)
SerrePositivity/InfinityCategories/F2/Compact/ColimitClosureExchange.lean:29:    (hK : CoherentFilteredLimitExchangeShape K.op) : IsKappaCompact.{u, v} κ a.vertex := by
SerrePositivity/InfinityCategories/F2/Compact/FiniteColimitClosure.lean:28:    (hκ : Cardinal.aleph0 ≤ κ) (hex : Ind.IndFiniteLimitExchangeInput.{max u v})
SerrePositivity/InfinityCategories/F2/Compact/FiniteColimitClosure.lean:37:    (hκ : Cardinal.aleph0 ≤ κ) (hex : Ind.IndFiniteLimitExchangeInput.{max u v})
SerrePositivity/InfinityCategories/F2/CoherentFilteredExchangeIso.lean:24:    (hK : CoherentFilteredLimitExchangeShape K) : CoherentFilteredLimitExchangeShape L := by
SerrePositivity/InfinityCategories/F2/CoherentFilteredExchangeIso.lean:42:    CoherentFilteredLimitExchangeShape K ↔ CoherentFilteredLimitExchangeShape L :=
SerrePositivity/InfinityCategories/F2/CoherentFilteredSimplexExchange.lean:24:    CoherentFilteredLimitExchangeShape (Δ[n] : SSet.{u}) := by
SerrePositivity/InfinityCategories/F2/SpaceLimitShapes.lean:24:def HasSpaceLimitsOfShape (K : SSet.{u}) : Prop :=
SerrePositivity/InfinityCategories/F2/SpaceLimitShapes.lean:29:    (hK : HasSpaceLimitsOfShape K) : HasSpaceLimitsOfShape L := by
SerrePositivity/InfinityCategories/F2/SpaceLimitShapes.lean:44:    HasSpaceLimitsOfShape K := by
SerrePositivity/InfinityCategories/F2/SpaceLimitShapes.lean:55:    HasSpaceLimitsOfShape (⊥ : X.Subcomplex) := by
SerrePositivity/InfinityCategories/F2/SpaceLimitShapes.lean:62:    HasSpaceLimitsOfShape (Δ[n] : SSet.{u}) := by
SerrePositivity/InfinityCategories/F2/Ind/FiniteYonedaColimitPreservation.lean:22:    (hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
SerrePositivity/InfinityCategories/F2/Ind/FiniteYonedaOppositeLimits.lean:22:variable (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
SerrePositivity/InfinityCategories/F2/Ind/FiniteConeExactness.lean:28:    (c : JoinCone D) (hc : IsLimitCone c) (hK : CoherentFilteredLimitExchangeShape K)
SerrePositivity/InfinityCategories/F2/Ind/FiniteConeExactness.lean:50:    (hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
SerrePositivity/InfinityCategories/F2/Ind/FiniteCoconeSections.lean:31:    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
SerrePositivity/InfinityCategories/F2/Ind/FiniteIndCommaSections.lean:47:    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
SerrePositivity/InfinityCategories/F2/Ind/OppositeUnstraighteningSections.lean:21:variable (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
SerrePositivity/InfinityCategories/F2/Ind/FiniteColimitExactness.lean:24:    (hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
SerrePositivity/InfinityCategories/F2/Ind/FiniteColimitExactness.lean:34:    (hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
SerrePositivity/InfinityCategories/F2/Ind/FiniteLimitExchangeInput.lean:18:structure IndFiniteLimitExchangeInput : Prop where
SerrePositivity/InfinityCategories/F2/Ind/FiniteLimitExchangeInput.lean:19:  exchange (K : SSet.{u}) [K.Finite] : CoherentFilteredLimitExchangeShape K
SerrePositivity/InfinityCategories/F2/Ind/FiniteYonedaSliceSections.lean:24:    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
SerrePositivity/KST/NonConnective.lean:7:public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
```
