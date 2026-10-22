module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComplex

/-! gluing の同じ実 Hom 複体を、νf と gμ の間の path 複体へ写す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomCompositionEndpoints (X Y : DGGluingObject R C D M) :=
  biprod.lift (biprod.fst ≫ dgGluingLeftAction R C D M X Y)
    (biprod.snd ≫ dgGluingRightAction R C D M X Y)

def dgGluingHomTwoEndpointPath (X Y : DGGluingObject R C D M) :
    dgGluingHomComplex R C D M X Y ⟶ dgGluingComplexPath (M.value X.left Y.right) :=
  dgGluingCoconeTwoEndpointPath (biprod.fst ≫ dgGluingLeftAction R C D M X Y)
    (biprod.snd ≫ dgGluingRightAction R C D M X Y)

lemma dgGluingHomTwoEndpointPath_start (X Y : DGGluingObject R C D M) :
    dgGluingHomTwoEndpointPath R C D M X Y ≫ dgGluingComplexPathStart (M.value X.left Y.right) =
      dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y := by
  exact dgGluingCoconeTwoEndpointPath_start _ _

lemma dgGluingHomTwoEndpointPath_end (X Y : DGGluingObject R C D M) :
    dgGluingHomTwoEndpointPath R C D M X Y ≫ dgGluingComplexPathEnd (M.value X.left Y.right) =
      dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y := by
  exact dgGluingCoconeTwoEndpointPath_end _ _

lemma dgGluingHomTwoEndpointPath_primitive (X Y : DGGluingObject R C D M) :
    (Cochain.ofHom (dgGluingHomTwoEndpointPath R C D M X Y)).comp
      (dgGluingComplexPathPrimitive (M.value X.left Y.right)) (zero_add (-1)) =
      dgGluingHomPrimitive R C D M X Y :=
  dgGluingCoconeTwoEndpointPath_primitive _ _

lemma dgGluingHomTwoEndpointPath_isPullback (X Y : DGGluingObject R C D M) :
    IsPullback (dgGluingHomTwoEndpointPath R C D M X Y)
      (mappingCocone.fst (dgGluingDifference R C D M X Y))
      (dgGluingComplexPathEndpoints (M.value X.left Y.right))
      (dgGluingHomCompositionEndpoints R C D M X Y) :=
  dgGluingTwoEndpointPath_isPullback _ _

end SerrePositivity.InfinityCategories
