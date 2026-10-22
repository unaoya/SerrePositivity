module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientIntervalPath

/-! 元の gluing Hom 空間から、二作用を両端とする係数空間内の通常 path 引き戻しへの比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomCoefficientPathPullback (X Y : DGGluingObject R C D M) :=
  pullback
    (F2.arrowEndpointPair (complexPinchedSpace.{u, max u v w} (M.value X.left Y.right)))
    (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y) ⊗ₘ
      complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y))

def dgGluingHomCoefficientPathPullbackComparison (X Y : DGGluingObject R C D M) :
    complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y) ⟶
      dgGluingHomCoefficientPathPullback R C D M X Y :=
  pullback.lift (dgGluingHomCoefficientIntervalPath R C D M X Y)
    (lift (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))
      (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) (by
        rw [dgGluingHomCoefficientIntervalPath_endpoints]
        exact (dgGluingHomTwoEndpointProduct_isPullback R C D M X Y).w)

lemma dgGluingHomCoefficientPathPullbackComparison_path (X Y : DGGluingObject R C D M) :
    dgGluingHomCoefficientPathPullbackComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingHomCoefficientIntervalPath R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingHomCoefficientPathPullbackComparison_inputs (X Y : DGGluingObject R C D M) :
    dgGluingHomCoefficientPathPullbackComparison R C D M X Y ≫ pullback.snd _ _ =
      lift (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
