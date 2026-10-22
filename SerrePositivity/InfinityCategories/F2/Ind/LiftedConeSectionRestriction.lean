module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedConePointedRestriction

/-!
概要：小さい left fibration 上の全錐の切断制限同値を、同じ native 全錐の宇宙持ち上げへ移す。
方針：相対切断の宇宙同型と、元の join の形状同型を合成する。
規約：構造射は証明済みの left fibration。底や形状の有限性を要求しない。
使われ方：小さい元の圏と大きい Yoneda slice の全比較への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 同じ小さい全錐の切断制限同値は、同じ native な持ち上げ全錐でも成り立つ。 -/
lemma leftFibrationConeRestriction_isQCatEquivalence_ulift
    {K E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {D : K ⟶ B} (c : JoinCone D)
    (h : IsQCatEquivalence (leftFibrationConeRestriction p c)) :
    IsQCatEquivalence (leftFibrationConeRestriction ((SSet.uliftFunctor.{u + 1, u}).map p)
      (JoinCone.ulift.{u, u + 1} c)) := by
  let g := Over.homMk (U := Over.mk D) (V := Over.mk c.val)
    (joinInr (Δ[0] : SSet.{u}) K) c.property
  have hg : IsQCatEquivalence (relativeFunctorOverPre p g) := by
    rw [← leftFibrationConeRestriction_eq_overPre]
    exact h
  have hu := relativeFunctorOverPre_isQCatEquivalence_ulift.{u, u + 1} p g hg
  let q := (SSet.uliftFunctor.{u + 1, u}).map p
  have : LeftFibration q := inferInstanceAs
    (LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map p))
  let e := liftedConeShapeOverIso c
  let ep : relativeFunctorSpace q (JoinCone.ulift.{u, u + 1} c).val ≅
      relativeFunctorSpace q ((SSet.uliftFunctor.{u + 1, u}).map c.val) :=
    (relativeFunctorOverFunctor q).mapIso e.op
  have he : IsQCatEquivalence (relativeFunctorOverPre q e.hom) :=
    (qCatEquivalenceOfIso ep).isQCatEquivalence
  rw [leftFibrationConeRestriction_eq_overPre, ← liftedConeShapeOverIso_restriction c,
    relativeFunctorOverPre_comp]
  exact he.comp hu

end SerrePositivity.InfinityCategories.F2.Ind
