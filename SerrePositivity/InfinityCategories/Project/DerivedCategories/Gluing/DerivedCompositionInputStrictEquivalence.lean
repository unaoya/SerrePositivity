module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DerivedLastInputDiagonalFibration
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DerivedCompositionInputStrictComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StrictPathPullbackEquivalence

/-! 元の左右 Hom 入力を保つ厳密合成対角引き戻しと、同じ全 path 模型の同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingDerivedCompositionInputStrictPathComparison_equivalence
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y) := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber] at hf
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber_kanComplex R C D M X Y
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber] at hl
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal_fibration R C D M X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictPathPullbackMap_equivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
