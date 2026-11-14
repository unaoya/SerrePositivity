module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KernelComparisonFunctor

/-! 直接表示した dg 関手の対象を型に保持する、同じ native/kernel Hom 同型。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonFunctor R C D M

/-- 関手の対象型を固定した、同じ全 Hom 鎖同型。 -/
def dgGluingKernelComparisonHomIso : homObject R G X Y ≅
    homObject R E ((F).obj X) ((F).obj Y) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Y

/-- 関手の全 Hom 写像は、同じ型で固定した同型の順射。 -/
lemma dgGluingKernelComparisonHomIso_map :
    (F).map X Y = (dgGluingKernelComparisonHomIso R C D M X Y).hom := rfl

/-- 同型の逆は、元の native/kernel 逆写像と厳密に同じ。 -/
lemma dgGluingKernelComparisonHomIso_inv :
    (dgGluingKernelComparisonHomIso R C D M X Y).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Y).inv := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
