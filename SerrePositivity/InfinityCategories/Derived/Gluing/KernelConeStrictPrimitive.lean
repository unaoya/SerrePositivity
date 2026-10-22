module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeKernelInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConePost

/-! 標準 kernel 円錐の厳密包含の後合成は、元の第三 cochain の同じ係数移送。 -/
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
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => dgGluingKernelObject R C D M X
local notation "KZ" => dgGluingKernelObject R C D M Z
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "i" => dgGluingKernelConeInr R C D M Y Z f

/-- native Hom を kernel Hom に送ってから閉包含で後合成した第三 cochain の厳密な式。 -/
lemma dgGluingKernelConeInr_post_primitive :
    (Cochain.ofHom ((dgGluingKernelHomIso R C D M X Z).hom ≫
      dgGluingKernelConePost R C D M X Y Z f)).comp
      (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX L)
      (zero_add (-1)) =
    (dgGluingHomPrimitive R C D M X Z).comp
      (Cochain.ofHom ((dgGluingKernelHomTargetIso R C D M X Z).hom ≫
        eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R) (representable R X.left))
          (dgGluingCommaPostImageArrow R (RightModule R D) (RightModule R C) F KZ L i)))
      (add_zero (-1)) := by
  dsimp only [dgGluingKernelConePost]
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [dgGluingCommaPost_of_comparison_zero R (RightModule R D) (RightModule R C)
    F KX KZ L i (dgGluingKernelConeInr_comparison R C D M Y Z f)]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingKernelHomIso_primitive, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp]
  rfl

end SerrePositivity.InfinityCategories
