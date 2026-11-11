module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RepresentablePresheafLimitDetection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits

/-!
概要：C の共変表現可能関手 Hom(x,−) を、反転を明示して同じ Hom 関手から構成する。
方針：C の二重反転の逆同型を Cᵒᵖ の表現可能前層へ合成する。
規約：始域は元の C の宇宙持ち上げ。反変前層と共変関手を区別する。
使われ方：F1-5 の元の C 上の極限の特徴づけ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の C 上の共変表現可能関手。二重反転の逆同型を明示して始域を揃える。 -/
def covariantRepresentableInfinity (x : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctorCompOpFunctorIso.app C).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (C := C.op) (SSet.opObjEquiv.symm x)

/-- 元の全錐の共変表現可能像と、二重反転した同じ全錐の表現可能前層像は同じ極限性を持つ。 -/
lemma covariantRepresentableInfinity_isLimit_iff_opposite {K : SSet.{u}} {D : K ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (covariantRepresentableInfinity x) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (C := C.op) (SSet.opObjEquiv.symm x))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (SSet.opFunctorCompOpFunctorIso.app C).inv c))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq
  · simp only [covariantRepresentableInfinity, Functor.map_comp, Category.assoc]
  · change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso K 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map c.val) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctorCompOpFunctorIso.app C).inv ≫ _) =
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso K 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (c.val ≫ (SSet.opFunctorCompOpFunctorIso.app C).inv)) ≫ _
    simp only [Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
