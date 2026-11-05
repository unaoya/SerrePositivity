module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputDiagonals

/-! 元の左右 Hom 入力を保持する対角 path 引き戻しと、同じ gluing Hom からの実比較。 -/
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

def dgGluingDerivedCompositionInputPathPullback (X Y : DGGluingObject R C D M) :=
  pullback (F2.arrowEndpointPair (intervalMappingSpace
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right)))))
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ⊗ₘ
      dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)

def dgGluingHomDerivedCompositionInputPathComparison (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingDerivedCompositionInputPathPullback R C D M X Y :=
  pullback.lift (dgGluingHomDerivedCompositionDiagonalPath R C D M X Y)
    (lift (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y)) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, F2.arrowEndpointPair, lift_fst, tensorHom_fst,
          lift_fst_assoc]
        exact (dgGluingHomDerivedCompositionDiagonalPath_start R C D M X Y).trans
          (dgGluingHomDerivedLastCompositionInputLift_diagonal R C D M X Y).symm
      · simp only [Category.assoc, F2.arrowEndpointPair, lift_snd, tensorHom_snd,
          lift_snd_assoc]
        exact (dgGluingHomDerivedCompositionDiagonalPath_end R C D M X Y).trans
          (dgGluingHomDerivedFirstCompositionInputLift_diagonal R C D M X Y).symm)

lemma dgGluingHomDerivedCompositionInputPathComparison_path (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionInputPathComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingHomDerivedCompositionDiagonalPath R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingHomDerivedCompositionInputPathComparison_compositions
    (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionInputPathComparison R C D M X Y ≫ pullback.snd _ _ =
      lift (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
        (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y) :=
  pullback.lift_snd _ _ _

lemma dgGluingHomDerivedCompositionInputPair_raw (X Y : DGGluingObject R C D M) :
    lift (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
        (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y) ≫
      (dgGluingDerivedLastCompositionInputProjection R C D M X Y ⊗ₘ
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y) =
    lift
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst]
    exact dgGluingHomDerivedLastCompositionInputLift_input R C D M X Y
  · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd]
    exact dgGluingHomDerivedFirstCompositionInputLift_input R C D M X Y

lemma dgGluingHomDerivedCompositionInputPathComparison_raw (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionInputPathComparison R C D M X Y ≫ pullback.snd _ _ ≫
      (dgGluingDerivedLastCompositionInputProjection R C D M X Y ⊗ₘ
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y) =
    lift
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) := by
  rw [← Category.assoc, dgGluingHomDerivedCompositionInputPathComparison_compositions R C D M X Y,
    dgGluingHomDerivedCompositionInputPair_raw R C D M X Y]

end SerrePositivity.InfinityCategories
