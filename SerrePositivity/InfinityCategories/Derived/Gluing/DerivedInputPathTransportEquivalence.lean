module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputPathTransport

/-! 同じ全係数 path と左右入力切断からなる引き戻し輸送は、実ホモトピー同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingDerivedCompositionInputPathTransport_equivalence
    (X Y : DGGluingObject R C D M) :
    IsSimplicialHomotopyEquivalence
      (dgGluingDerivedCompositionInputPathTransport R C D M X Y) := by
  have := F2.kanComplex_tensor
    (complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left))
    (complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right))
  have hf := dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  have hl := dgGluingDerivedLastCompositionInputFiber_kanComplex R C D M X Y
  have ht := F2.kanComplex_tensor (dgGluingDerivedLastCompositionInputFiber R C D M X Y)
    (dgGluingDerivedFirstCompositionInputFiber R C D M X Y)
  have ht' := ht
  dsimp only [dgGluingDerivedLastCompositionInputFiber,
    dgGluingDerivedFirstCompositionInputFiber] at hf hl ht'
  have hp : KanComplex (dgGluingDerivedHomCoefficientPathPullback R C D M X Y) :=
    dgGluingKanPathPullback_kanComplex _
  dsimp only [dgGluingDerivedHomCoefficientPathPullback] at hp
  have := dgGluingKanPathPullback_kanComplex
    (dgGluingDerivedHomCoefficientActions R C D M X Y ≫
      (dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right ⊗ₘ
        dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right))
  have htarget : KanComplex (dgGluingDerivedCompositionInputPathPullback R C D M X Y) :=
    dgGluingKanPathPullback_kanComplex _
  have htarget' := htarget
  dsimp only [dgGluingDerivedCompositionInputPathPullback] at htarget'
  exact (dgGluingKanPathPullbackTransport_equivalence _ _
    (dgGluingDerivedCoefficientIntervalMap_equivalence R C D M X.left Y.right)).comp
      (dgGluingKanPathInputTransport_equivalence _ _ _
        (dgGluingDerivedCompositionInputPairSection_diagonals R C D M X Y)
        (dgGluingDerivedCompositionInputPairSection_equivalence R C D M X Y))

end SerrePositivity.InfinityCategories
