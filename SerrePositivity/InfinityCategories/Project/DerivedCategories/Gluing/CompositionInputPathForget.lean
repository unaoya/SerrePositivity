module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCompositionInputPathPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCompositionPathPullback

/-! 元 Hom 入力の制限を忘れると、同じ二合成対応と全対角 path の比較へ戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingCompositionInputPairForget (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  pullback.fst
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLeftCoefficientInput R C D M X Y) ⊗ₘ
    pullback.fst
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.right))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedRightCoefficientInput R C D M X Y)

lemma dgGluingCompositionInputPairForget_diagonals (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingCompositionInputPairForget R C D M X Y ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left)))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionDiagonal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.right)))) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y := by
  rw [dgGluingCompositionInputPairForget, tensorHom_comp_tensorHom]
  rfl

def dgGluingCompositionInputPathForget (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPathPullback R C D M X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionPathPullback R C D M X Y :=
  pullback.map _ _ _ _ (𝟙 _) (dgGluingCompositionInputPairForget R C D M X Y) (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, dgGluingCompositionInputPairForget_diagonals R C D M X Y])

lemma dgGluingCompositionInputPathForget_path (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingCompositionInputPathForget R C D M X Y ≫ pullback.fst _ _ = pullback.fst _ _ := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

lemma dgGluingCompositionInputPathForget_compositions (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingCompositionInputPathForget R C D M X Y ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ dgGluingCompositionInputPairForget R C D M X Y :=
  pullback.lift_snd _ _ _

lemma dgGluingHomDerivedCompositionInputPair_forget (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift R C D M X Y) ≫
      dgGluingCompositionInputPairForget R C D M X Y =
    lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastComposition R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstComposition R C D M X Y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingCompositionInputPairForget, Category.assoc, tensorHom_fst,
      lift_fst]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift_composition R C D M X Y
  · simp only [dgGluingCompositionInputPairForget, Category.assoc, tensorHom_snd,
      lift_snd]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift_composition R C D M X Y

lemma dgGluingHomDerivedCompositionInputPathComparison_forget (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionInputPathComparison R C D M X Y ≫
        dgGluingCompositionInputPathForget R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionPathComparison R C D M X Y := by
  apply pullback.hom_ext
  · rw [Category.assoc, dgGluingCompositionInputPathForget_path,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionInputPathComparison_path,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionPathComparison_path]
  · rw [Category.assoc, dgGluingCompositionInputPathForget_compositions, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionInputPathComparison_compositions,
      dgGluingHomDerivedCompositionInputPair_forget R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionPathComparison_inputs]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
