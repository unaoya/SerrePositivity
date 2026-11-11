module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DerivedCompositionInputPairSection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KanPathInputTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCompositionInputPathPullback

/-! 同じ係数全 path を区間 Hom へ移し、具体的な左右入力切断で入力付き path 模型へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedCompositionInputPathTransport (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientPathPullback R C D M X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPathPullback R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientActions R C D M X Y) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathInputTransport _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPairSection R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPairSection_diagonals R C D M X Y)

lemma dgGluingDerivedCompositionInputPathTransport_path (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputPathTransport R C D M X Y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (ihom (Δ[1] : SSet.{max (u + 1) v w})).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientIntervalMap R C D M X.left Y.right) := by
  rw [dgGluingDerivedCompositionInputPathTransport, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathInputTransport_path, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport_path]

lemma dgGluingDerivedCompositionInputPathTransport_inputs (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputPathTransport R C D M X Y ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPairSection R C D M X Y := by
  rw [dgGluingDerivedCompositionInputPathTransport, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathInputTransport_inputs, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport_inputs]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
