module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorClosedCosliceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetUnitLiftComparison
/-!
概要：同じ Hom 単位の元の実 coslice 比較は、全ての実 fiber で同値。
方針：同じ合成 Hom 鎖写像が dg Yoneda の逆であることを、元の実 fiber 判定へ適用する。
規約：点ごとの抽象空間同値ではなく、構成済みの同じ実 fiber 射を証明する。
使われ方：Hom の pointed 表示の全 fiber 同値と全関手比較への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C)
/-- 同じ Hom 単位から構成した元の実 coslice 比較は、各実対象上の fiber で全空間同値。 -/
lemma dgHomTargetCosliceComparison_fiber_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R C)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison R C x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison_projection R C x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnitLiftHomMap_isIso R C x y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorClosedCosliceRawFiber_isQCatEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x)
    x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R C) y
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x))
/-- 同じ実 coslice 比較の全ての実頂点 fiber 射は全空間同値。 -/
lemma dgHomTargetCosliceComparison_fibers_isQCatEquivalence (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R C)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison R C x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison_projection R C x) b) := by
  obtain ⟨z, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := C)).symm.surjective b
  exact dgHomTargetCosliceComparison_fiber_isQCatEquivalence R C x z
end SerrePositivity.InfinityCategories.Project.DerivedCategories
