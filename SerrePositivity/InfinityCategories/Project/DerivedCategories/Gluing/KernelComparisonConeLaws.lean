module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelComparisonConeModels
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.GradedPostFactorization

/-! 型を固定した同じ円錐データの、左包含と指定境界元の像の二法則。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonFunctor R C D M
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f

/-- 同じ左包含の全次数作用公式。 -/
lemma dgGluingKernelComparisonConeIso_inl (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonConeInl R C D M Y Z f X).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonConeIso R C D M Y Z f X).hom)
      (add_zero (-1)) =
    (Cochain.ofHom ((F).map X Y)).comp
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E ((F).obj X) ((F).obj Y) L).f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonNullElement R C D M Y Z f)) (zero_add (-1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonCone_inl R C D M Y Z f X

variable
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q

/-- 同じ native 境界元を、同じ閉代表射で送った像の公式。 -/
lemma dgGluingKernelComparisonNullElement_image :
    ((F).map Y W).f (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonNativeNullElement R C D M Y Z f p q) =
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) ((F).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonRepresentativeMap R C D M Y Z f p q)).f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonNullElement R C D M Y Z f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonCone_null R C D M Y Z f p q

/-- 指定境界元の像の条件を、同じ名前付き命題で固定する。 -/
lemma dgGluingKernelComparisonNullImageCondition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostImageCondition R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) E F Y W L
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonRepresentativeMap R C D M Y Z f p q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonNullElement R C D M Y Z f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonNativeNullElement R C D M Y Z f p q) :=
  dgGluingKernelComparisonNullElement_image R C D M Y Z f p q

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
