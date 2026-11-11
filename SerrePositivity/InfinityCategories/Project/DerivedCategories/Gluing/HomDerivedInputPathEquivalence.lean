module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedInputPathFactorization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DerivedInputPathTransportEquivalence

/-! 元の左右 Hom 射影と元の全係数 path を持つ保存済み入力付き比較そのものの同値性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedCompositionInputPathComparison_equivalence
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionInputPathComparison R C D M X Y) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right))
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber_kanComplex R C D M X Y
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber R C D M X Y)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber] at hf hl ht
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientPathPullback R C D M X Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullback_kanComplex _
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPathPullback R C D M X Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullback_kanComplex _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionInputPathComparison_factor R C D M X Y]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientPathComparison_equivalence R C D M X Y).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPathTransport_equivalence R C D M X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
