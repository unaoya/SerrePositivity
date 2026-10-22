module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeKernelLeftAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.GradedPostFactorization
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeNativeRepresentation
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeNullElementKernel
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelComparisonConeLaws

/-! 指定 native 境界元の作用を、同じ実円錐比較と代表射に因子分解する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => DGGluingObject R C D M
local notation "F" => dgGluingKernelComparisonFunctor R C D M
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "a" => dgGluingKernelComparisonRepresentativeMap R C D M Y Z f p q

/-- 指定 native 境界元の作用は、同じ円錐比較・代表射・Hom 逆同型の合成。 -/
lemma dgGluingConeNullPost_factorization :
    (dgGluingGradedPostcomposition R G X Y W).f (-1)
      (dgGluingConeNullElement R C D M Y Z f p q) =
    (mappingCone.inl (dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom ((dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
        dgGluingKernelConeRepresentativePost R C D M Y Z f p q
          (dgGluingKernelObject R C D M X) ≫ (dgGluingKernelHomIso R C D M X W).inv))
      (add_zero (-1)) := by
  have hi := dgGluingKernelComparisonConeIso_inl R C D M Y Z f X
  have hg := dgGluingKernelComparisonNullImageCondition R C D M Y Z f p q
  have hf := dgGluingGradedPost_factorization R G E F X Y W L a
    (dgGluingKernelComparisonHomIso R C D M X W)
    (dgGluingKernelComparisonHomIso_map R C D M X W)
    (P := mappingCone (dgGluingPostcomposition R C D M X Y Z f))
    (dgGluingKernelComparisonConeInl R C D M Y Z f X)
    (dgGluingKernelComparisonConeIso R C D M Y Z f X).hom
    (dgGluingKernelComparisonNullElement R C D M Y Z f)
    (dgGluingKernelComparisonNativeNullElement R C D M Y Z f p q) hi hg
  simpa only [dgGluingKernelComparisonFunctor, dgGluingKernelComparisonHomIso_inv,
    dgGluingKernelComparisonConeIso, dgGluingKernelComparisonRepresentativeMap,
    dgGluingKernelComparisonConeInl, dgGluingKernelComparisonNativeNullElement,
    dgGluingKernelConeRepresentativePost] using! hf

end SerrePositivity.InfinityCategories
