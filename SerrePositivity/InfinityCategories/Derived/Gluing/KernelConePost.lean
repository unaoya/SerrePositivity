module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeRightArrow

/-! 標準 kernel 円錐への同じ閉包含による、始域・標的を固定した実 Hom 後合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)

/-- 元の Hom 鎖写像と同じ順の実 kernel Hom 後合成。 -/
def dgGluingKernelConePost :
    dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) (dgGluingKernelObject R C D M X)
      (dgGluingKernelObject R C D M Z) ⟶
    dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) (dgGluingKernelObject R C D M X)
      (dgGluingKernelConeObject R C D M Y Z f) :=
  eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (dgGluingKernelObject R C D M X))
    (Y := ForgetEnrichment.of (Complex R) (dgGluingKernelObject R C D M Z))
    (Y' := ForgetEnrichment.of (Complex R) (dgGluingKernelConeObject R C D M Y Z f))
    (dgGluingKernelConeInr R C D M Y Z f)

end SerrePositivity.InfinityCategories
