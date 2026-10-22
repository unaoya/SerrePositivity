module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeNullElementKernel
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaGradedPostcomposition

/-! 指定した kernel 境界元の作用と、同じ円錐代表射による後合成との結合則。 -/
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
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => DGGluingObject R C D M
local notation "F" => Morita.kernelTensor R D C M
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "KW" => dgGluingKernelObject R C D M W
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "a" => dgGluingKernelConeRepresentativeMap R C D M Y Z f p q
variable (X : DGGluingObject R C D M)
local notation "KX" => dgGluingKernelObject R C D M X
local notation "postX" => dgGluingKernelConeRepresentativePost R C D M Y Z f p q KX

include X in
/-- 代表射で移した kernel 境界元の作用は、元の同じ作用と代表射の後合成。 -/
abbrev dgGluingKernelConeRepresentativeNullPost :=
  dgGluingCommaGradedPostcomposition_postcompose R (RightModule R D) (RightModule R C)
    F KX KY L KW a (dgGluingKernelConeNullElement R C D M Y Z f)

include X in
/-- native/kernel Hom 比較による閉前合成を含めた、同じ代表射の後合成の因子分解。 -/
abbrev dgGluingKernelConeRepresentativeNullPrePost :=
  dgGluingCommaGradedPostcomposition_pre_post R (RightModule R D) (RightModule R C)
    F KX KY L KW a (dgGluingKernelConeNullElement R C D M Y Z f)
    (dgGluingHomComplex R C D M X Y) (dgGluingKernelHomIso R C D M X Y).hom

end SerrePositivity.InfinityCategories
