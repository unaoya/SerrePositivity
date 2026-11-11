module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ShiftModuleMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomModuleEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelShiftRepresentativeHomotopy
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-! 同じ全 dg 自然なシフト加群比較自身の objectwise quasi-isomorphism 性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (n : ℤ)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R C X.left n)
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingShiftRepresentative R D X.right n)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomModuleFunctor R C D M
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftRepresentativeMap R C D M X n p q

/-- 同じ代表閉射の制限 Hom 加群像は、全対象で quasi-isomorphism。 -/
lemma dgGluingKernelShiftRepresentativeModule_quasiIso :
    moduleQuasiIso R G ((J).onClosed.map a) := by
  intro Z
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomModuleFunctor_closed_eval]
  change QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftRepresentativePost R C D M X n p q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Z))
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftRepresentativePostEquiv_hom]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftRepresentativePostEquiv R C D M X n p q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Z)).quasiIso_hom

/-- 標準シフト同型と代表加群同型を戻した同じ実加群射も quasi-isomorphism。 -/
lemma dgGluingShiftModuleMap_quasiIso :
    moduleQuasiIso R G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftModuleMap R C D M X n p q) := by
  intro Z
  have hq := dgGluingKernelShiftRepresentativeModule_quasiIso R C D M X n p q Z
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftModuleMap, CategoryTheory.Functor.map_comp]
  infer_instance

omit p q in
/-- 元の両圏の前三角性を明示入力に持つ、同じ選択版の quasi-isomorphism 性。 -/
lemma dgGluingChosenShiftModuleMap_quasiIso
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    moduleQuasiIso R G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChosenShiftModuleMap R C D M X n hC hD) :=
  dgGluingShiftModuleMap_quasiIso R C D M X n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseShiftRepresentative R C X.left n hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseShiftRepresentative R D X.right n hD)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
