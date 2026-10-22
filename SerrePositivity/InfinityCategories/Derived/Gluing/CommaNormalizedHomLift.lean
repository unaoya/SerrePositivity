module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaNormalizedHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaHomLift

/-! 実閉射による正規化と、同じ二作用・primitive の明示 mapping-cocone lift は厳密に一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : DGFunctorCommaObject R C E F)

abbrev dgGluingCommaNormalizedSource :
    dgFunctorCommaHomComplex R C E F X Y ⟶ homObject R E X.replacement (F.obj Y.source) :=
  dgFunctorCommaImageHomMap R C E F X Y ≫
    eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj Y.source))

abbrev dgGluingCommaNormalizedReplacement :
    dgFunctorCommaHomComplex R C E F X Y ⟶ homObject R E X.replacement (F.obj Y.source) :=
  dgFunctorCommaReplacementHomMap R C E F X Y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement) Y.augmentation

lemma dgGluingCommaNormalizedPrimitive_boundary :
    δ (-1) 0 (dgFunctorCommaPrimitive R C E F X Y) +
      Cochain.ofHom (dgGluingCommaNormalizedSource R C E F X Y -
        dgGluingCommaNormalizedReplacement R C E F X Y) = 0 :=
  dgFunctorCommaPrimitive_boundary R C E F X Y

def dgGluingCommaNormalizedHomLift :
    dgFunctorCommaHomComplex R C E F X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement)
        (dgGluingIdentityCommaObject R E (F.obj Y.source)) :=
  dgGluingIdentityCommaHomLift R E X.replacement (F.obj Y.source) _
    (dgGluingCommaNormalizedSource R C E F X Y)
    (dgGluingCommaNormalizedReplacement R C E F X Y)
    (dgFunctorCommaPrimitive R C E F X Y)
    (dgGluingCommaNormalizedPrimitive_boundary R C E F X Y)

lemma dgGluingCommaNormalizedHom_eq_lift :
    dgGluingCommaNormalizedHom R C E F X Y = dgGluingCommaNormalizedHomLift R C E F X Y := by
  apply dgFunctorCommaHom_ext R E E (DGFunctor.id E)
    (dgGluingIdentityCommaObject R E X.replacement)
    (dgGluingIdentityCommaObject R E (F.obj Y.source)) _
  · rw [dgGluingCommaNormalizedHomLift, dgGluingIdentityCommaHomLift_source,
      dgGluingCommaNormalizedHom_source]
  · rw [dgGluingCommaNormalizedHomLift, dgGluingIdentityCommaHomLift_replacement,
      dgGluingCommaNormalizedHom_replacement]
  · change (Cochain.ofHom (dgGluingCommaNormalizedHom R C E F X Y)).comp
        (dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _) (zero_add (-1)) =
      (Cochain.ofHom (dgGluingCommaNormalizedHomLift R C E F X Y)).comp
        (dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _) (zero_add (-1))
    rw [dgGluingCommaNormalizedHomLift, dgGluingCommaNormalizedHom_primitive,
      dgGluingIdentityCommaHomLift_primitive]

end SerrePositivity.InfinityCategories
