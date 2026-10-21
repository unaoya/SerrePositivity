module
public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedConePointedRestriction
public import SerrePositivity.InfinityCategories.Derived.LeftTransportConeRestriction
/-!
概要：元の全錐の切断制限を、持ち上げた native 錐と分類図式の同じ制限へ移す。
方針：元の相対関手の宇宙同型と join の形状同型を、両方向で消去する。
規約：極限錐の選択を変えない。使われ方：dg Hom 試験の極限判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet HomotopyLimits
open scoped Simplicial
/-- 元の全錐の実切断制限の宇宙比較。 -/
lemma leftFibrationConeRestriction_ulift_iff
    {K E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {d : K ⟶ B} (c : JoinCone d) :
    IsQCatEquivalence (leftFibrationConeRestriction p c) ↔
      IsQCatEquivalence (leftFibrationConeRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map p) (JoinCone.ulift.{u, u + 1} c)) := by
  let g := Over.homMk (U := Over.mk d) (V := Over.mk c.val)
    (joinInr (Δ[0] : SSet.{u}) K) c.property
  let e := liftedConeShapeOverIso c
  let ep : relativeFunctorSpace ((SSet.uliftFunctor.{u + 1, u}).map p)
      (JoinCone.ulift.{u, u + 1} c).val ≅
    relativeFunctorSpace ((SSet.uliftFunctor.{u + 1, u}).map p)
      ((SSet.uliftFunctor.{u + 1, u}).map c.val) :=
    (relativeFunctorOverFunctor ((SSet.uliftFunctor.{u + 1, u}).map p)).mapIso e.op
  have he : IsQCatEquivalence (relativeFunctorOverPre
      ((SSet.uliftFunctor.{u + 1, u}).map p) e.hom) :=
    (qCatEquivalenceOfIso ep).isQCatEquivalence
  have hn : leftFibrationConeRestriction ((SSet.uliftFunctor.{u + 1, u}).map p)
      (JoinCone.ulift.{u, u + 1} c) =
    relativeFunctorOverPre ((SSet.uliftFunctor.{u + 1, u}).map p) e.hom ≫
      relativeFunctorOverPre ((SSet.uliftFunctor.{u + 1, u}).map p) (uliftOverMorphism g) := by
    rw [leftFibrationConeRestriction_eq_overPre,
      ← liftedConeShapeOverIso_restriction, relativeFunctorOverPre_comp]
  rw [hn, leftFibrationConeRestriction_eq_overPre]
  constructor
  · intro h
    exact he.comp (relativeFunctorOverPre_isQCatEquivalence_ulift p g h)
  · intro h
    exact relativeFunctorOverPre_isQCatEquivalence_of_ulift p g (he.cancel_left h)
/-- 元の全錐の実切断制限の宇宙比較。 -/
lemma LeftTransportRepresentation.uliftConeRestriction_iff
    {K E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    {d : K ⟶ B} (c : JoinCone d) :
    IsQCatEquivalence (leftFibrationConeRestriction p c) ↔
      IsQCatEquivalence (leftFibrationConeRestriction pointedSpaceProjection
        (mapJoinCone R.diagram (JoinCone.ulift.{u, u + 1} c))) :=
  (leftFibrationConeRestriction_ulift_iff p c).trans
    (LeftTransportRepresentation.coneRestriction_iff
      ((SSet.uliftFunctor.{u + 1, u}).map p) R (JoinCone.ulift.{u, u + 1} c))
end SerrePositivity.InfinityCategories
