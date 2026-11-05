module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionDiagonalPath

/-! 元の Hom を、同じ二合成対応とその対角間 path の実引き戻しへ送る。 -/
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

def dgGluingDerivedCompositionPathPullback (X Y : DGGluingObject R C D M) :=
  pullback (F2.arrowEndpointPair (intervalMappingSpace
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right)))))
    (compositionCorrespondenceDiagonal
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.left)))
        (dgGluingDerivedAugmentationEdge R C D M Y) ⊗ₘ
      dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right))))

def dgGluingHomDerivedCompositionPathComparison (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingDerivedCompositionPathPullback R C D M X Y :=
  pullback.lift (dgGluingHomDerivedCompositionDiagonalPath R C D M X Y)
    (lift (dgGluingHomDerivedLastComposition R C D M X Y)
      (dgGluingHomDerivedFirstComposition R C D M X Y)) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, F2.arrowEndpointPair, lift_fst, tensorHom_fst,
          lift_fst_assoc]
        exact dgGluingHomDerivedCompositionDiagonalPath_start R C D M X Y
      · simp only [Category.assoc, F2.arrowEndpointPair, lift_snd, tensorHom_snd,
          lift_snd_assoc]
        exact dgGluingHomDerivedCompositionDiagonalPath_end R C D M X Y)

lemma dgGluingHomDerivedCompositionPathComparison_path (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionPathComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingHomDerivedCompositionDiagonalPath R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingHomDerivedCompositionPathComparison_inputs (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionPathComparison R C D M X Y ≫ pullback.snd _ _ =
      lift (dgGluingHomDerivedLastComposition R C D M X Y)
        (dgGluingHomDerivedFirstComposition R C D M X Y) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
