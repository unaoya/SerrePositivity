module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedInputPathFactorization
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedInputPathTransportEquivalence

/-! 元の左右 Hom 射影と元の全係数 path を持つ保存済み入力付き比較そのものの同値性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedCompositionInputPathComparison_equivalence
    (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomDerivedCompositionInputPathComparison R C D M X Y) := by
  have := F2.kanComplex_tensor
    (complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left))
    (complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right))
  have hf := dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  have hl := dgGluingDerivedLastCompositionInputFiber_kanComplex R C D M X Y
  have ht := F2.kanComplex_tensor (dgGluingDerivedLastCompositionInputFiber R C D M X Y)
    (dgGluingDerivedFirstCompositionInputFiber R C D M X Y)
  dsimp only [dgGluingDerivedLastCompositionInputFiber,
    dgGluingDerivedFirstCompositionInputFiber] at hf hl ht
  have : KanComplex (dgGluingDerivedHomCoefficientPathPullback R C D M X Y) :=
    dgGluingKanPathPullback_kanComplex _
  have : KanComplex (dgGluingDerivedCompositionInputPathPullback R C D M X Y) :=
    dgGluingKanPathPullback_kanComplex _
  rw [dgGluingHomDerivedCompositionInputPathComparison_factor R C D M X Y]
  exact (dgGluingDerivedHomCoefficientPathComparison_equivalence R C D M X Y).comp
    (dgGluingDerivedCompositionInputPathTransport_equivalence R C D M X Y)

end SerrePositivity.InfinityCategories
