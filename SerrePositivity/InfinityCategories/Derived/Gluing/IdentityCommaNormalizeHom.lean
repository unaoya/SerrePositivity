module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaNormalizationPrimitive

/-! 二標準閉射の実前後合成は、両恒等 augmentation 間の同じ二作用・比較 cochain を持つ Hom 射。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))

def dgGluingIdentityCommaNormalizeHom :
    dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement)
          (dgGluingIdentityCommaObject R E Y.source) :=
  dgGluingIdentityCommaPreNormalizeHom R E X Y ≫
    dgGluingIdentityCommaPostNormalizeHom R E (dgGluingIdentityCommaObject R E X.replacement) Y

lemma dgGluingIdentityCommaNormalizeHom_source :
    dgGluingIdentityCommaNormalizeHom R E X Y ≫
        dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
          (dgGluingIdentityCommaObject R E X.replacement)
          (dgGluingIdentityCommaObject R E Y.source) =
      dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) X Y ≫
        eHomWhiskerRight (Complex R) X.augmentation (ForgetEnrichment.of (Complex R) Y.source) := by
  rw [dgGluingIdentityCommaNormalizeHom, Category.assoc,
    dgGluingIdentityCommaPostNormalizeHom_source, dgGluingIdentityCommaPreNormalizeHom_source]

lemma dgGluingIdentityCommaNormalizeHom_replacement :
    dgGluingIdentityCommaNormalizeHom R E X Y ≫
        dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
          (dgGluingIdentityCommaObject R E X.replacement)
          (dgGluingIdentityCommaObject R E Y.source) =
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) X Y ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
          Y.augmentation := by
  rw [dgGluingIdentityCommaNormalizeHom, Category.assoc,
    dgGluingIdentityCommaPostNormalizeHom_replacement, ← Category.assoc,
    dgGluingIdentityCommaPreNormalizeHom_replacement]

lemma dgGluingIdentityCommaNormalizeHom_primitive :
    (Cochain.ofHom (dgGluingIdentityCommaNormalizeHom R E X Y)).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement)
          (dgGluingIdentityCommaObject R E Y.source))
      (zero_add (-1)) = dgFunctorCommaPrimitive R E E (DGFunctor.id E) X Y := by
  rw [dgGluingIdentityCommaNormalizeHom, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, dgGluingIdentityCommaPostNormalizeHom_primitive,
    dgGluingIdentityCommaPreNormalizeHom_primitive]

lemma dgGluingIdentityCommaNormalizeHom_comparison (K : Complex R)
    (f : K ⟶ dgFunctorCommaHomComplex R E E (DGFunctor.id E) X Y) :
    dgFunctorCommaHomComparison R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E X.replacement)
          (dgGluingIdentityCommaObject R E Y.source) K
        (f ≫ dgGluingIdentityCommaNormalizeHom R E X Y) =
      dgFunctorCommaHomComparison R E E (DGFunctor.id E) X Y K f := by
  change (Cochain.ofHom (f ≫ dgGluingIdentityCommaNormalizeHom R E X Y)).comp
    (dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _) (zero_add (-1)) = _
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingIdentityCommaNormalizeHom_primitive]
  rfl

end SerrePositivity.InfinityCategories
