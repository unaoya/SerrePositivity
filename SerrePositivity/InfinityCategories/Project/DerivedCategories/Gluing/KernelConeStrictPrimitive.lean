module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeKernelInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelConePost

/-! 標準 kernel 円錐の厳密包含の後合成は、元の第三 cochain の同じ係数移送。 -/
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
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X
local notation "KZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Z
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "i" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr R C D M Y Z f

/-- native Hom を kernel Hom に送ってから閉包含で後合成した第三 cochain の厳密な式。 -/
lemma dgGluingKernelConeInr_post_primitive :
    (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Z).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConePost R C D M X Y Z f)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX L)
      (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Z).comp
      (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomTargetIso R C D M X Z).hom ≫
        eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R) (representable R X.left))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R (RightModule R D) (RightModule R C) F KZ L i)))
      (add_zero (-1)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConePost]
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_of_comparison_zero R (RightModule R D) (RightModule R C)
    F KX KZ L i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr_comparison R C D M Y Z f)]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso_primitive, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
