module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCommaCoconeLifts
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeFilteredCriterion
public import SerrePositivity.InfinityCategories.F2.Ind.LiftedPointQuillenA
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredWeakContractibility
public import SerrePositivity.InfinityCategories.Core.InnerPullback

/-!
概要：指定された小さい像余錐を厳密に持ち上げる写像の right cofinal 性を判定する。
方針：元の指定変換下の実引き戻しに全余錐を作り、同じ写像へ Quillen A を適用する。
規約：元の像余錐自身の回収を要求し、存在だけでは結論しない。
使われ方：極大点を追加した元の diagram comma から既存部分への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {X Y : SSet.{u + 1}}
  [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
  (hY : ∀ {B : SSet.{u}}, IsKappaSmall κ B →
    ∀ f : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ Y, Nonempty (JoinCocone f))
  (hF : ∀ {B : SSet.{u}}, IsKappaSmall κ B →
    ∀ f : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X,
    ∀ G : JoinCocone (f ≫ F), ∃ c : JoinCocone f, mapJoinCocone F c = G)
include hY hF
/-- 概要：元の指定像の下の実引き戻しは filtered。
方針：厳密な像余錐持ち上げ。規約：元の指定族。使われ方：Quillen A の入力。 -/
lemma underComma_isFiltered_of_cocone_lifts {L : SSet.{u}} (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ Y) :
    IsFilteredInfinity (pullback (sliceUnderProjection z) F) := by
  apply isFilteredInfinity_of_liftedShape_cocones (Fact.out : κ.IsRegular)
  intro A hA q
  have h : (q ≫ pullback.snd (sliceUnderProjection z) F) ≫ F =
      (q ≫ pullback.fst (sliceUnderProjection z) F) ≫ sliceUnderProjection z := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hc := nonempty_relativeComma_cocone_of_cocone_lifts F hY hF hA hL z
    (q ≫ pullback.snd (sliceUnderProjection z) F)
    (q ≫ pullback.fst (sliceUnderProjection z) F) h
  have hq : relativeCommaFamily F z (q ≫ pullback.fst (sliceUnderProjection z) F)
      (q ≫ pullback.snd (sliceUnderProjection z) F) h = q := by
    apply pullback.hom_ext <;> simp only [relativeCommaFamily, pullback.lift_fst,
      pullback.lift_snd]
  exact hq ▸ hc
/-- 概要：小さい指定像余錐を厳密に持ち上げる元の写像は right cofinal。
方針：実 under comma の弱可縮性。規約：同じ元の写像。使われ方：各点密度の伝播。 -/
lemma isRightCofinal_of_cocone_lifts : IsRightCofinal F := by
  apply isRightCofinal_of_weaklyContractible_lifted_point_under
  intro z
  have := underComma_isFiltered_of_cocone_lifts F hY hF
    (isKappaSmall_of_finite (Fact.out : κ.IsRegular).aleph0_le (Δ[0] : SSet.{u})) z
  exact isWeaklyContractible_of_isFilteredInfinity _
end SerrePositivity.InfinityCategories.F2.Ind
