module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomModuleShift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelRepresentableModule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelShiftRepresentatives

/-! 同じ標準シフトと代表射から、全 dg 自然な実 Yoneda 加群シフト比較を構成する。 -/
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
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R C X.left n)
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R D X.right n)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftObjectFromRepresentatives R C D M X n p q
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomModuleFunctor R C D M

/-- 標準シフト同型、同じ代表閉射、kernel/native 同型の合成による実加群射。 -/
def dgGluingShiftModuleMap :
    ForgetEnrichment.of (Complex R) (shiftModule n (representable R X)) ⟶
      ForgetEnrichment.of (Complex R) (representable R W) :=
  ((moduleShiftFunctor R G n).mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelRepresentableModuleIso R C D M X)).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomModuleShiftIso R C D M X n).inv ≫
    (J).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftRepresentativeMap R C D M X n p q) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelRepresentableModuleIso R C D M W).inv

/-- 元の両圏の前三角性を明示入力に取る、選んだ同じ gluing シフトへの加群比較。 -/
def dgGluingChosenShiftModuleMap
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    ForgetEnrichment.of (Complex R) (shiftModule n (representable R X)) ⟶
      ForgetEnrichment.of (Complex R) (representable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftObject R C D M X n hC hD)) :=
  dgGluingShiftModuleMap R C D M X n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseShiftRepresentative R C X.left n hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseShiftRepresentative R D X.right n hD)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
