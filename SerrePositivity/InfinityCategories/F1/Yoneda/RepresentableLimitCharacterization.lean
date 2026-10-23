module

public import SerrePositivity.InfinityCategories.F1.Yoneda.CovariantRepresentableInfinity

/-!
概要：元の C の小さい全錐の極限性を、全共変表現可能関手の同じ像によって特徴づける。
方針：二重反転の同型を通じて Cᵒᵖ の表現可能前層の検出定理を適用する。
規約：元の全錐を保ち、図式や脚の反転を省略しない。
使われ方：F1-5、HTT 5.1.3.2。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の小さい全錐が極限であることと、全 Hom(x,−) の同じ像が極限であることは同値。 -/
lemma isLimitCone_iff_covariantRepresentableInfinity {K C : SSet.{u}} [Quasicategory C]
    {D : K ⟶ C} (c : JoinCone D) :
    IsLimitCone c ↔ ∀ x : C _⦋0⦌,
      IsLimitCone (mapJoinCone (covariantRepresentableInfinity x) (JoinCone.ulift.{u, u + 1} c)) := by
  let e : C ≅ C.op.op := (SSet.opFunctorCompOpFunctorIso.app C).symm
  have he := (qCatEquivalenceOfIso e).isQCatEquivalence.isLimitCone_iff c
  have hr := isLimitCone_iff_representablePresheafInfinity (C := C.op) (mapJoinCone e.hom c)
  constructor
  · intro hc x
    apply (covariantRepresentableInfinity_isLimit_iff_opposite c x).mpr
    exact hr.mp (he.mp hc) (SSet.opObjEquiv.symm x)
  · intro hc
    apply he.mpr
    apply hr.mpr
    intro y
    have h := (covariantRepresentableInfinity_isLimit_iff_opposite c (SSet.opObjEquiv y)).mp
      (hc (SSet.opObjEquiv y))
    have hy : SSet.opObjEquiv.symm (SSet.opObjEquiv y) = y := Equiv.symm_apply_apply _ y
    rw [hy] at h
    exact h

/-- 元の共変表現可能関手は、小さい形状の元の極限全錐を保存する。 -/
lemma covariantRepresentableInfinity_isLimit {K C : SSet.{u}} [Quasicategory C]
    {D : K ⟶ C} (c : JoinCone D) (hc : IsLimitCone c) (x : C _⦋0⦌) :
    IsLimitCone (mapJoinCone (covariantRepresentableInfinity x) (JoinCone.ulift.{u, u + 1} c)) :=
  (isLimitCone_iff_covariantRepresentableInfinity c).mp hc x

/-- 全共変表現可能関手での極限性は、同じ元の全錐の極限性を検出する。 -/
lemma isLimitCone_of_covariantRepresentableInfinity {K C : SSet.{u}} [Quasicategory C]
    {D : K ⟶ C} (c : JoinCone D)
    (hc : ∀ x : C _⦋0⦌,
      IsLimitCone (mapJoinCone (covariantRepresentableInfinity x) (JoinCone.ulift.{u, u + 1} c))) :
    IsLimitCone c :=
  (isLimitCone_iff_covariantRepresentableInfinity c).mpr hc

end SerrePositivity.InfinityCategories
