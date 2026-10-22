module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointProductPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTwoEndpointPath

/-! 元の gluing Hom の空間模型を、左右 Hom と係数 Hom の実直積を使って表示する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomTwoEndpointProduct_isPullback (X Y : DGGluingObject R C D M) :
    IsPullback
      (complexPinchedMap.{u, max u v w} (dgGluingHomTwoEndpointPath R C D M X Y))
      (lift (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)))
      (dgGluingComplexPathSpaceEndpointPair.{u, max u v w} (M.value X.left Y.right))
      (complexPinchedMap.{u, max u v w} (dgGluingLeftAction R C D M X Y) ⊗ₘ
        complexPinchedMap.{u, max u v w} (dgGluingRightAction R C D M X Y)) :=
  dgGluingTwoEndpointProduct_isPullback _ _

end SerrePositivity.InfinityCategories
