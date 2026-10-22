module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelComparisonFunctor
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeKernelLeftAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeNullElementKernel

/-! 同じ左包含と指定境界元の比較を、対象・Hom を直接指定した dg 関手の型で回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => dgGluingKernelComparisonFunctor R C D M
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "L" => dgGluingKernelConeObject R C D M Y Z f

/-- 左包含の作用公式を、同じ直接表示の dg 関手の Hom 型で固定する。 -/
lemma dgGluingKernelComparisonCone_inl (X : DGGluingObject R C D M) :
    (mappingCone.inl (dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (dgGluingHomConeKernelIso R C D M X Y Z f).hom) (add_zero (-1)) =
    (Cochain.ofHom ((F).map X Y)).comp
      ((dgGluingGradedPostcomposition R E ((F).obj X) ((F).obj Y) L).f (-1)
        (dgGluingKernelConeNullElement R C D M Y Z f)) (zero_add (-1)) :=
  dgGluingHomConeKernelIso_inl R C D M X Y Z f

variable
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "a" => dgGluingKernelConeRepresentativeMap R C D M Y Z f p q

/-- 指定 native 境界元の像も、同じ直接表示の Hom 型で固定する。 -/
lemma dgGluingKernelComparisonCone_null :
    ((F).map Y W).f (-1) (dgGluingConeNullElement R C D M Y Z f p q) =
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) ((F).obj Y)) a).f (-1)
      (dgGluingKernelConeNullElement R C D M Y Z f) := by
  have hg := dgGluingConeNullElement_kernel R C D M Y Z f p q
  rw [dgGluingKernelConeRepresentativeNullElement, dgGluingKernelConeRepresentativePost] at hg
  exact hg

end SerrePositivity.InfinityCategories
