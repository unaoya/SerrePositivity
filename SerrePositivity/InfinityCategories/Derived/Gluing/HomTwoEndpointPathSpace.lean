module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathSpaceLimit
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTwoEndpointPath

/-! 元の実 gluing Hom の空間模型を、νf と gμ を端点とする ∞ 引き戻しとして供給する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomTwoEndpointPathSpace_isPullback (X Y : DGGluingObject R C D M) :
    IsPullback (complexPinchedMap.{u, max u v w} (dgGluingHomTwoEndpointPath R C D M X Y))
      (complexPinchedMap.{u, max u v w} (mappingCocone.fst (dgGluingDifference R C D M X Y)))
      (complexPinchedMap.{u, max u v w} (dgGluingComplexPathEndpoints (M.value X.left Y.right)))
      (complexPinchedMap.{u, max u v w} (dgGluingHomCompositionEndpoints R C D M X Y)) :=
  dgGluingComplexPinchedMap_isPullback (dgGluingHomTwoEndpointPath_isPullback R C D M X Y)

def dgGluingHomTwoEndpointPathSpaceCone (X Y : DGGluingObject R C D M) :=
  dgGluingTwoEndpointPathSpaceCone.{u, max u v w}
    (biprod.fst ≫ dgGluingLeftAction R C D M X Y)
    (biprod.snd ≫ dgGluingRightAction R C D M X Y)

lemma dgGluingHomTwoEndpointPathSpaceCone_isLimit (X Y : DGGluingObject R C D M) :
    IsLimitCone (dgGluingHomTwoEndpointPathSpaceCone R C D M X Y) :=
  dgGluingTwoEndpointPathSpaceCone_isLimit _ _

lemma dgGluingHomTwoEndpointPathSpaceCone_vertex (X Y : DGGluingObject R C D M) :
    (dgGluingHomTwoEndpointPathSpaceCone R C D M X Y).vertex =
      F2.coherentVertex (dgGluingComplexPinchedKanObject.{u, max u v w}
        (dgGluingHomComplex R C D M X Y)) :=
  dgGluingTwoEndpointPathSpaceCone_vertex _ _

end SerrePositivity.InfinityCategories
