module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaGeneralDifference
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaComparison

/-! 任意関手の comma を、その同じ実 augmentation を持つ標的恒等 comma へ移す全 Hom 鎖写像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)

def dgGluingCommaImageObject (X : DGFunctorCommaObject R C E F) :
    DGFunctorCommaObject R E E (DGFunctor.id E) where
  source := F.obj X.source
  replacement := X.replacement
  augmentation := X.augmentation

lemma dgGluingCommaImage_difference (X Y : DGFunctorCommaObject R C E F) :
    biprod.lift (dgFunctorCommaImageHomMap R C E F X Y)
        (dgFunctorCommaReplacementHomMap R C E F X Y) ≫
      dgFunctorCommaDifference R E E (DGFunctor.id E)
        (dgGluingCommaImageObject R C E F X) (dgGluingCommaImageObject R C E F Y) =
      dgFunctorCommaBoundary R C E F X Y :=
  dgGluingIdentityCommaGeneralDifference_lift R E _ _ _ _ _

def dgGluingCommaImageHomMap (X Y : DGFunctorCommaObject R C E F) :
    dgFunctorCommaHomComplex R C E F X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (dgGluingCommaImageObject R C E F X) (dgGluingCommaImageObject R C E F Y) :=
  dgFunctorCommaHomLift R E E (DGFunctor.id E) _ _ _
    (dgFunctorCommaImageHomMap R C E F X Y) (dgFunctorCommaReplacementHomMap R C E F X Y)
    (dgFunctorCommaPrimitive R C E F X Y) (by
      rw [dgGluingCommaImage_difference]
      exact dgFunctorCommaPrimitive_boundary R C E F X Y)

end SerrePositivity.InfinityCategories
