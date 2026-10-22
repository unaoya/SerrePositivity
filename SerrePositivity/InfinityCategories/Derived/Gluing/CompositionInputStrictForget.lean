module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputStrictComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalStrictForget

/-! 入力付き厳密対角引き戻しから元の矢印 Hom の二合成対応への忘却と、主比較の厳密回収。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingCompositionInputStrictForget (X Y : DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputStrictPullback R C D M X Y ⟶
      dgGluingArrowCompositionPullback (dgGluingDerivedAugmentationEdge R C D M X)
        (dgGluingDerivedAugmentationEdge R C D M Y) :=
  dgGluingRestrictedDiagonalStrictForget
    (compositionCorrespondenceFirst
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (compositionCorrespondenceDiagonal
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y))
    (dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))))
    (dgGluingDerivedLeftCoefficientInput R C D M X Y)
    (dgGluingDerivedRightCoefficientInput R C D M X Y)

lemma dgGluingCompositionInputStrictForget_first (X Y : DGGluingObject R C D M) :
    dgGluingCompositionInputStrictForget R C D M X Y ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ :=
  dgGluingRestrictedDiagonalStrictForget_first _ _ _ _ _ _

lemma dgGluingCompositionInputStrictForget_last (X Y : DGGluingObject R C D M) :
    dgGluingCompositionInputStrictForget R C D M X Y ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  dgGluingRestrictedDiagonalStrictForget_last _ _ _ _ _ _

lemma dgGluingLaxHomInputStrictComparison_forget (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomInputStrictComparison R C D M X Y ≫
        dgGluingCompositionInputStrictForget R C D M X Y =
      dgGluingLaxHomArrowCompositionComparison R C D M X Y := by
  apply pullback.hom_ext
  · rw [Category.assoc, dgGluingCompositionInputStrictForget_first R C D M X Y,
      ← Category.assoc, dgGluingLaxHomInputStrictComparison_first R C D M X Y,
      dgGluingLaxHomFirstCompositionInputLift_composition R C D M X Y]
  · rw [Category.assoc, dgGluingCompositionInputStrictForget_last R C D M X Y,
      ← Category.assoc, dgGluingLaxHomInputStrictComparison_last R C D M X Y,
      dgGluingLaxHomLastCompositionInputLift_composition R C D M X Y]

end SerrePositivity.InfinityCategories
