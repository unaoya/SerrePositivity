module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageFunctor
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizeHom

/-! 元 comma の同じ二作用と primitive は、実標準閉射の前後合成で恒等 comma に回収される。 -/
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
local notation "IX" => dgGluingCommaImageObject R C E F X
local notation "IY" => dgGluingCommaImageObject R C E F Y

def dgGluingCommaNormalizedHom :
    dgFunctorCommaHomComplex R C E F X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement)
        (dgGluingIdentityCommaObject R E (F.obj Y.source)) :=
  dgGluingCommaImageHomMap R C E F X Y ≫ dgGluingIdentityCommaNormalizeHom R E IX IY

lemma dgGluingCommaNormalizedHom_source :
    dgGluingCommaNormalizedHom R C E F X Y ≫
      dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement)
        (dgGluingIdentityCommaObject R E (F.obj Y.source)) =
      dgFunctorCommaImageHomMap R C E F X Y ≫
        eHomWhiskerRight (Complex R) X.augmentation
          (ForgetEnrichment.of (Complex R) (F.obj Y.source)) := by
  change (dgGluingCommaImageHomMap R C E F X Y ≫
    dgGluingIdentityCommaNormalizeHom R E IX IY) ≫
      dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E (dgGluingCommaImageObject R C E F X).replacement)
        (dgGluingIdentityCommaObject R E (dgGluingCommaImageObject R C E F Y).source) = _
  rw [Category.assoc,
    dgGluingIdentityCommaNormalizeHom_source R E IX IY, ← Category.assoc,
    dgGluingCommaImageHomMap_source]
  rfl

lemma dgGluingCommaNormalizedHom_replacement :
    dgGluingCommaNormalizedHom R C E F X Y ≫
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement)
        (dgGluingIdentityCommaObject R E (F.obj Y.source)) =
      dgFunctorCommaReplacementHomMap R C E F X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
          Y.augmentation := by
  change (dgGluingCommaImageHomMap R C E F X Y ≫
    dgGluingIdentityCommaNormalizeHom R E IX IY) ≫
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E (dgGluingCommaImageObject R C E F X).replacement)
        (dgGluingIdentityCommaObject R E (dgGluingCommaImageObject R C E F Y).source) = _
  rw [Category.assoc,
    dgGluingIdentityCommaNormalizeHom_replacement R E IX IY, ← Category.assoc,
    dgGluingCommaImageHomMap_replacement]
  rfl

lemma dgGluingCommaNormalizedHom_primitive :
    (Cochain.ofHom (dgGluingCommaNormalizedHom R C E F X Y)).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement)
        (dgGluingIdentityCommaObject R E (F.obj Y.source))) (zero_add (-1)) =
      dgFunctorCommaPrimitive R C E F X Y := by
  change (Cochain.ofHom (dgGluingCommaImageHomMap R C E F X Y ≫
    dgGluingIdentityCommaNormalizeHom R E IX IY)).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E (dgGluingCommaImageObject R C E F X).replacement)
        (dgGluingIdentityCommaObject R E (dgGluingCommaImageObject R C E F Y).source))
      (zero_add (-1)) = _
  rw [Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingIdentityCommaNormalizeHom_primitive R E IX IY,
    dgGluingCommaImageHomMap_primitive]

end SerrePositivity.InfinityCategories
