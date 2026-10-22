module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeKernelLeftAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeNullPostFactorization
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeModuleMapRightComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeNullElementKernel
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelComparisonConeData

/-! 実加群円錐射と点ごとの native Hom 同値の順射は、指定した同じ左包含上で一致する。 -/
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
local notation "a" => dgGluingKernelConeRepresentativeMap R C D M Y Z f p q

/-- 加群円錐射の左評価は、点ごとの同値の同じ順射の左包含と厳密に一致。 -/
lemma dgGluingConeModuleMapEvaluation_inl_comparison :
    (mappingCone.inl (dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (dgGluingConeModuleMapEvaluation R C D M Y Z f p q X))
      (add_zero (-1)) =
    (mappingCone.inl (dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f p q).hom)
      (add_zero (-1)) := by
  rw [dgGluingConeModuleMapEvaluation_inl, dgGluingHomConeNativeRepresentativeEquiv_hom]
  exact dgGluingConeNullPost_factorization R C D M X Y Z f p q

end SerrePositivity.InfinityCategories
