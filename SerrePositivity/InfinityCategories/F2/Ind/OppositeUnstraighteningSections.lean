module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteCoconeSections
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedConeSectionRestriction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening

/-!
概要：同じ有限全余錐の切断制限を、元の right unstraightening の反転へ移す。
方針：元の反転全空間の底上の厳密な同型と、全錐の宇宙持ち上げを使う。
規約：交換入力と元の指定余錐を保持。使われ方：元の Yoneda slice 比較への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
  {K C : SSet.{u}} [K.Finite] [Quasicategory C] {D : K ⟶ C}
  (c : JoinCocone D) (hc : IsColimitCone c)
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
  (hF : IsIndVertex κ C (functorVertex F))
include hκ hex hc hF

/-- 元の right unstraightening の反転上で、同じ反転全錐の切断制限自身が同値。 -/
lemma indPresheaf_finiteColimit_oppositeRightSections_isQCatEquivalence :
    IsQCatEquivalence (leftFibrationConeRestriction
      (SSet.opFunctor.map (smallRightUnstraighteningProjection F))
      (F1B.kanCoconeReverseCone c)) := by
  have hs : IsQCatEquivalence (leftFibrationConeRestriction
      (smallLeftUnstraighteningProjection F) (F1B.kanCoconeReverseCone c)) := by
    rw [leftFibrationConeRestriction_eq_overPre]
    exact indPresheaf_finiteColimit_smallSectionRestriction_isQCatEquivalence κ hκ hex c hc F hF
  exact (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (SSet.opFunctor.map (smallRightUnstraighteningProjection F))
    (smallLeftUnstraighteningProjection F) (smallRightUnstraighteningOppositeIso F).hom
    (smallRightUnstraighteningProjection_op F).symm
    (isPrecompositionEquivalence_of_iso (smallRightUnstraighteningOppositeIso F))
    (F1B.kanCoconeReverseCone c)).mpr hs

/-- 元の反転全錐と全空間の同じ宇宙持ち上げでも、元の切断制限が同値。 -/
lemma indPresheaf_finiteColimit_liftedOppositeRightSections_isQCatEquivalence :
    IsQCatEquivalence (leftFibrationConeRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (smallRightUnstraighteningProjection F)))
      (JoinCone.ulift.{u, u + 1} (F1B.kanCoconeReverseCone c))) :=
  leftFibrationConeRestriction_isQCatEquivalence_ulift _ _
    (indPresheaf_finiteColimit_oppositeRightSections_isQCatEquivalence κ hκ hex c hc F hF)

end SerrePositivity.InfinityCategories.F2.Ind
