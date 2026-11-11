module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeKernelLeftComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelConeNullhomotopy

/-! 指定 kernel 零 cochain の両成分を、単位と同じ加群円錐左包含で回収する。 -/
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
local notation "F" => Morita.kernelTensor R D C M
local notation "KY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "h" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullCochain R C D M Y Z f
local notation "P" => ForgetEnrichment.of (Complex R) (representable R Y.left)
local notation "Q" => ForgetEnrichment.of (Complex R) (representable R Y.right)
local notation "lf" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)

/-- 指定零 cochain の source 成分は、右単位の Yoneda 像と同じ加群円錐左包含。 -/
lemma dgGluingKernelConeNullCochain_source :
    (h).comp (Cochain.ofHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F KY L))
      (add_zero (-1)) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentity R C D M Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M Y Y ≫
      yonedaHom R D Y.right Y.right)).comp
      (moduleHomConeLeftCochain R D Q rf) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullCochain, Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso_inl_source]
  simp only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

/-- 指定零 cochain の replacement 成分も、左単位と同じ加群円錐左包含。 -/
lemma dgGluingKernelConeNullCochain_replacement :
    (h).comp (Cochain.ofHom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F KY L))
      (add_zero (-1)) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentity R C D M Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M Y Y ≫
      yonedaHom R C Y.left Y.left)).comp
      (moduleHomConeLeftCochain R C P lf) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullCochain, Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso_inl_replacement]
  simp only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
