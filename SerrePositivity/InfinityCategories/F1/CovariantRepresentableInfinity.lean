module

public import SerrePositivity.InfinityCategories.F1.RepresentablePresheafLimitDetection
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-!
概要：C の共変表現可能関手 Hom(x,−) を、反転を明示して同じ Hom 関手から構成する。
方針：C の二重反転の逆同型を Cᵒᵖ の表現可能前層へ合成する。
規約：始域は元の C の宇宙持ち上げ。反変前層と共変関手を区別する。
使われ方：F1-5 の元の C 上の極限の特徴づけ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の C 上の共変表現可能関手。二重反転の逆同型を明示して始域を揃える。 -/
def covariantRepresentableInfinity (x : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctorCompOpFunctorIso.app C).inv ≫
    representablePresheafInfinity (C := C.op) (SSet.opObjEquiv.symm x)

/-- 元の全錐の共変表現可能像と、二重反転した同じ全錐の表現可能前層像は同じ極限性を持つ。 -/
lemma covariantRepresentableInfinity_isLimit_iff_opposite {K : SSet.{u}} {D : K ⟶ C}
    (c : JoinCone D) (x : C _⦋0⦌) :
    IsLimitCone (mapJoinCone (covariantRepresentableInfinity x) (JoinCone.ulift.{u, u + 1} c)) ↔
    IsLimitCone (mapJoinCone (representablePresheafInfinity (C := C.op) (SSet.opObjEquiv.symm x))
      (JoinCone.ulift.{u, u + 1} (mapJoinCone (SSet.opFunctorCompOpFunctorIso.app C).inv c))) := by
  apply isLimitCone_iff_of_diagram_eq
  · simp only [covariantRepresentableInfinity, Functor.map_comp, Category.assoc]
  · change ((uliftConeShapeIso K 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map c.val) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctorCompOpFunctorIso.app C).inv ≫ _) =
      ((uliftConeShapeIso K 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (c.val ≫ (SSet.opFunctorCompOpFunctorIso.app C).inv)) ≫ _
    simp only [Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories
