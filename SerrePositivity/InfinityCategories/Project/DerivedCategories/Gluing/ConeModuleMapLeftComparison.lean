module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeKernelLeftAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeNullPostFactorization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeModuleMapRightComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeNullElementKernel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelComparisonConeData

/-! 実加群円錐射と点ごとの native Hom 同値の順射は、指定した同じ左包含上で一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonFunctor R C D M
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativeMap R C D M Y Z f p q

/-- 加群円錐射の左評価は、点ごとの同値の同じ順射の左包含と厳密に一致。 -/
lemma dgGluingConeModuleMapEvaluation_inl_comparison :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMapEvaluation R C D M Y Z f p q X))
      (add_zero (-1)) =
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeNativeRepresentativeEquiv R C D M X Y Z f p q).hom)
      (add_zero (-1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleMapEvaluation_inl, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeNativeRepresentativeEquiv_hom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeNullPost_factorization R C D M X Y Z f p q

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
