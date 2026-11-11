module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelComparisonFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeKernelLeftAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeNullElementKernel

/-! 同じ左包含と指定境界元の比較を、対象・Hom を直接指定した dg 関手の型で回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonFunctor R C D M
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f

/-- 左包含の作用公式を、同じ直接表示の dg 関手の Hom 型で固定する。 -/
lemma dgGluingKernelComparisonCone_inl (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M X Y Z f).hom) (add_zero (-1)) =
    (Cochain.ofHom ((F).map X Y)).comp
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E ((F).obj X) ((F).obj Y) L).f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement R C D M Y Z f)) (zero_add (-1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso_inl R C D M X Y Z f

variable
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativeMap R C D M Y Z f p q

/-- 指定 native 境界元の像も、同じ直接表示の Hom 型で固定する。 -/
lemma dgGluingKernelComparisonCone_null :
    ((F).map Y W).f (-1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeNullElement R C D M Y Z f p q) =
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) ((F).obj Y)) a).f (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement R C D M Y Z f) := by
  have hg := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeNullElement_kernel R C D M Y Z f p q
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativeNullElement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativePost] at hg
  exact hg

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
