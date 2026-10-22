module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointProductLimit
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTwoEndpointProduct

/-! 実 gluing Hom 自体の空間模型を、元の二つの作用の直積の ∞ 引き戻しに供給する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomTwoEndpointProductCone (X Y : DGGluingObject R C D M) :=
  dgGluingTwoEndpointProductCone.{u, max u v w} (dgGluingLeftAction R C D M X Y)
    (dgGluingRightAction R C D M X Y)

lemma dgGluingHomTwoEndpointProductCone_isLimit (X Y : DGGluingObject R C D M) :
    IsLimitCone (dgGluingHomTwoEndpointProductCone R C D M X Y) :=
  dgGluingTwoEndpointProductCone_isLimit _ _

lemma dgGluingHomTwoEndpointProductCone_vertex (X Y : DGGluingObject R C D M) :
    (dgGluingHomTwoEndpointProductCone R C D M X Y).vertex =
      F2.coherentVertex (dgGluingComplexPinchedKanObject.{u, max u v w}
        (dgGluingHomComplex R C D M X Y)) :=
  dgGluingTwoEndpointProductCone_vertex _ _

end SerrePositivity.InfinityCategories
