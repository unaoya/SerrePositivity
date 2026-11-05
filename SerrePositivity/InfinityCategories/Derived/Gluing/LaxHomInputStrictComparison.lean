module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomCompositionInputLifts
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputStrictComparison

/-! 元の lax Hom 比較を、左右 Hom 入力を保つ厳密な同一対角の引き戻しへ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxHomCompositionInputLift_diagonals (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomLastCompositionInputLift R C D M X Y ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y =
      dgGluingLaxHomFirstCompositionInputLift R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y := by
  rw [dgGluingDerivedLastCompositionInputDiagonal, ← Category.assoc,
    dgGluingLaxHomLastCompositionInputLift_composition R C D M X Y,
    dgGluingDerivedFirstCompositionInputDiagonal, ← Category.assoc,
    dgGluingLaxHomFirstCompositionInputLift_composition R C D M X Y]
  have hh := congrArg (fun k => dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ k)
    (pullback.condition
      (f := dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
        ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex Y.right))))
      (g := compositionCorrespondenceDiagonal
        ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
          (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y)))
  simpa only [Category.assoc] using hh.symm

def dgGluingLaxHomInputStrictComparison (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingDerivedCompositionInputStrictPullback R C D M X Y :=
  pullback.lift (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
    (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
    (dgGluingLaxHomCompositionInputLift_diagonals R C D M X Y)

lemma dgGluingLaxHomInputStrictComparison_last (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomInputStrictComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingLaxHomLastCompositionInputLift R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingLaxHomInputStrictComparison_first (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomInputStrictComparison R C D M X Y ≫ pullback.snd _ _ =
      dgGluingLaxHomFirstCompositionInputLift R C D M X Y :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
