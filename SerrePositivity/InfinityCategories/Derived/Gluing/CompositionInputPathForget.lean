module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionInputPathPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionPathPullback

/-! 元 Hom 入力の制限を忘れると、同じ二合成対応と全対角 path の比較へ戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingCompositionInputPairForget (X Y : DGGluingObject R C D M) :=
  pullback.fst
      (compositionCorrespondenceFirst
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.left)))
        (dgGluingDerivedAugmentationEdge R C D M Y))
      (dgGluingDerivedLeftCoefficientInput R C D M X Y) ⊗ₘ
    pullback.fst
      (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right))))
      (dgGluingDerivedRightCoefficientInput R C D M X Y)

lemma dgGluingCompositionInputPairForget_diagonals (X Y : DGGluingObject R C D M) :
    dgGluingCompositionInputPairForget R C D M X Y ≫
      (compositionCorrespondenceDiagonal
          ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex X.left)))
          (dgGluingDerivedAugmentationEdge R C D M Y) ⊗ₘ
        dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
          ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (DGNerve.Simplex.vertex Y.right)))) =
    dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ⊗ₘ
      dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y := by
  rw [dgGluingCompositionInputPairForget, tensorHom_comp_tensorHom]
  rfl

def dgGluingCompositionInputPathForget (X Y : DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputPathPullback R C D M X Y ⟶
      dgGluingDerivedCompositionPathPullback R C D M X Y :=
  pullback.map _ _ _ _ (𝟙 _) (dgGluingCompositionInputPairForget R C D M X Y) (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, dgGluingCompositionInputPairForget_diagonals R C D M X Y])

lemma dgGluingCompositionInputPathForget_path (X Y : DGGluingObject R C D M) :
    dgGluingCompositionInputPathForget R C D M X Y ≫ pullback.fst _ _ = pullback.fst _ _ := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

lemma dgGluingCompositionInputPathForget_compositions (X Y : DGGluingObject R C D M) :
    dgGluingCompositionInputPathForget R C D M X Y ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ dgGluingCompositionInputPairForget R C D M X Y :=
  pullback.lift_snd _ _ _

lemma dgGluingHomDerivedCompositionInputPair_forget (X Y : DGGluingObject R C D M) :
    lift (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
        (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y) ≫
      dgGluingCompositionInputPairForget R C D M X Y =
    lift (dgGluingHomDerivedLastComposition R C D M X Y)
      (dgGluingHomDerivedFirstComposition R C D M X Y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingCompositionInputPairForget, Category.assoc, tensorHom_fst,
      lift_fst]
    exact dgGluingHomDerivedLastCompositionInputLift_composition R C D M X Y
  · simp only [dgGluingCompositionInputPairForget, Category.assoc, tensorHom_snd,
      lift_snd]
    exact dgGluingHomDerivedFirstCompositionInputLift_composition R C D M X Y

lemma dgGluingHomDerivedCompositionInputPathComparison_forget (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionInputPathComparison R C D M X Y ≫
        dgGluingCompositionInputPathForget R C D M X Y =
      dgGluingHomDerivedCompositionPathComparison R C D M X Y := by
  apply pullback.hom_ext
  · rw [Category.assoc, dgGluingCompositionInputPathForget_path,
      dgGluingHomDerivedCompositionInputPathComparison_path,
      dgGluingHomDerivedCompositionPathComparison_path]
  · rw [Category.assoc, dgGluingCompositionInputPathForget_compositions, ← Category.assoc,
      dgGluingHomDerivedCompositionInputPathComparison_compositions,
      dgGluingHomDerivedCompositionInputPair_forget R C D M X Y,
      dgGluingHomDerivedCompositionPathComparison_inputs]

end SerrePositivity.InfinityCategories
