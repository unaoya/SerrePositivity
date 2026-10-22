module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelComparisonConeModels
public import SerrePositivity.InfinityCategories.Derived.Gluing.GradedPostFactorization

/-! 型を固定した同じ円錐データの、左包含と指定境界元の像の二法則。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "F" => dgGluingKernelComparisonFunctor R C D M
local notation "L" => dgGluingKernelConeObject R C D M Y Z f

/-- 同じ左包含の全次数作用公式。 -/
lemma dgGluingKernelComparisonConeIso_inl (X : DGGluingObject R C D M) :
    (dgGluingKernelComparisonConeInl R C D M Y Z f X).comp
      (Cochain.ofHom (dgGluingKernelComparisonConeIso R C D M Y Z f X).hom)
      (add_zero (-1)) =
    (Cochain.ofHom ((F).map X Y)).comp
      ((dgGluingGradedPostcomposition R E ((F).obj X) ((F).obj Y) L).f (-1)
        (dgGluingKernelComparisonNullElement R C D M Y Z f)) (zero_add (-1)) :=
  dgGluingKernelComparisonCone_inl R C D M Y Z f X

variable
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q

/-- 同じ native 境界元を、同じ閉代表射で送った像の公式。 -/
lemma dgGluingKernelComparisonNullElement_image :
    ((F).map Y W).f (-1) (dgGluingKernelComparisonNativeNullElement R C D M Y Z f p q) =
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) ((F).obj Y))
      (dgGluingKernelComparisonRepresentativeMap R C D M Y Z f p q)).f (-1)
        (dgGluingKernelComparisonNullElement R C D M Y Z f) :=
  dgGluingKernelComparisonCone_null R C D M Y Z f p q

/-- 指定境界元の像の条件を、同じ名前付き命題で固定する。 -/
lemma dgGluingKernelComparisonNullImageCondition :
    dgGluingGradedPostImageCondition R (DGGluingObject R C D M) E F Y W L
      (dgGluingKernelComparisonRepresentativeMap R C D M Y Z f p q)
      (dgGluingKernelComparisonNullElement R C D M Y Z f)
      (dgGluingKernelComparisonNativeNullElement R C D M Y Z f p q) :=
  dgGluingKernelComparisonNullElement_image R C D M Y Z f p q

end SerrePositivity.InfinityCategories
