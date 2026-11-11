module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelCommaObjects
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift

/-! 同じ通常 kernel の加群 comma 内で、両代表加群の任意整数シフトを組み立てる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (n : ℤ)
local notation "F" => Morita.kernelTensor R D C M

/-- 元の augmentation をシフトし、同じ通常 tensor の shift 同型で戻した実閉射。 -/
def dgGluingKernelShiftAugmentation :
    ForgetEnrichment.of (Complex R) (shiftModule n (representable R X.left)) ⟶
      ForgetEnrichment.of (Complex R) ((F).obj (shiftModule n (representable R X.right))) :=
  moduleShiftMap R C n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelLift R C D M X) ≫
    (normalizedDGModuleFunctorShiftIso R D C F n (representable R X.right)).inv

/-- 両側の同じ加群シフトと、移送した同じ augmentation を持つ標準 kernel 対象。 -/
def dgGluingKernelShiftObject :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C) F where
  source := shiftModule n (representable R X.right)
  replacement := shiftModule n (representable R X.left)
  augmentation := dgGluingKernelShiftAugmentation R C D M X n

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
