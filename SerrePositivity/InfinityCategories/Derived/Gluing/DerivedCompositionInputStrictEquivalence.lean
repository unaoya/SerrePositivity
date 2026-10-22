module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedLastInputDiagonalFibration
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputStrictComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.StrictPathPullbackEquivalence

/-! 元の左右 Hom 入力を保つ厳密合成対角引き戻しと、同じ全 path 模型の同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingDerivedCompositionInputStrictPathComparison_equivalence
    (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence
      (dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y) := by
  have hf := dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  dsimp only [dgGluingDerivedFirstCompositionInputFiber] at hf
  have hl := dgGluingDerivedLastCompositionInputFiber_kanComplex R C D M X Y
  dsimp only [dgGluingDerivedLastCompositionInputFiber] at hl
  have := dgGluingDerivedLastCompositionInputDiagonal_fibration R C D M X Y
  exact dgGluingStrictPathPullbackMap_equivalence
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)

end SerrePositivity.InfinityCategories
