module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputPairSection
public import SerrePositivity.InfinityCategories.Derived.Gluing.KanPathInputTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionInputPathPullback

/-! 同じ係数全 path を区間 Hom へ移し、具体的な左右入力切断で入力付き path 模型へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedCompositionInputPathTransport (X Y : DGGluingObject R C D M) :
    dgGluingDerivedHomCoefficientPathPullback R C D M X Y ⟶
      dgGluingDerivedCompositionInputPathPullback R C D M X Y :=
  dgGluingKanPathPullbackTransport
      (dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right)
      (dgGluingDerivedHomCoefficientActions R C D M X Y) ≫
    dgGluingKanPathInputTransport _
      (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ⊗ₘ
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
      (dgGluingDerivedCompositionInputPairSection R C D M X Y)
      (dgGluingDerivedCompositionInputPairSection_diagonals R C D M X Y)

lemma dgGluingDerivedCompositionInputPathTransport_path (X Y : DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputPathTransport R C D M X Y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (ihom (Δ[1] : SSet.{max (u + 1) v w})).map
        (dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right) := by
  rw [dgGluingDerivedCompositionInputPathTransport, Category.assoc,
    dgGluingKanPathInputTransport_path, dgGluingKanPathPullbackTransport_path]

lemma dgGluingDerivedCompositionInputPathTransport_inputs (X Y : DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputPathTransport R C D M X Y ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ dgGluingDerivedCompositionInputPairSection R C D M X Y := by
  rw [dgGluingDerivedCompositionInputPathTransport, Category.assoc,
    dgGluingKanPathInputTransport_inputs, ← Category.assoc,
    dgGluingKanPathPullbackTransport_inputs]

end SerrePositivity.InfinityCategories
