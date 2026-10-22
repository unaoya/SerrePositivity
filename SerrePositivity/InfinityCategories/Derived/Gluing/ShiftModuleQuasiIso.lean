module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ShiftModuleMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomModuleEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelShiftRepresentativeHomotopy
public import SerrePositivity.DifferentialGraded.Module.QuasiIso

/-! 同じ全 dg 自然なシフト加群比較自身の objectwise quasi-isomorphism 性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : DGGluingObject R C D M) (n : ℤ)
  (p : DGGluingShiftRepresentative R C X.left n)
  (q : DGGluingShiftRepresentative R D X.right n)
local notation "G" => DGGluingObject R C D M
local notation "J" => dgGluingKernelHomModuleFunctor R C D M
local notation "a" => dgGluingKernelShiftRepresentativeMap R C D M X n p q

/-- 同じ代表閉射の制限 Hom 加群像は、全対象で quasi-isomorphism。 -/
lemma dgGluingKernelShiftRepresentativeModule_quasiIso :
    moduleQuasiIso R G ((J).onClosed.map a) := by
  intro Z
  rw [dgGluingKernelHomModuleFunctor_closed_eval]
  change QuasiIso (dgGluingKernelShiftRepresentativePost R C D M X n p q
    (dgGluingKernelObject R C D M Z))
  rw [← dgGluingKernelShiftRepresentativePostEquiv_hom]
  exact (dgGluingKernelShiftRepresentativePostEquiv R C D M X n p q
    (dgGluingKernelObject R C D M Z)).quasiIso_hom

/-- 標準シフト同型と代表加群同型を戻した同じ実加群射も quasi-isomorphism。 -/
lemma dgGluingShiftModuleMap_quasiIso :
    moduleQuasiIso R G (dgGluingShiftModuleMap R C D M X n p q) := by
  intro Z
  have hq := dgGluingKernelShiftRepresentativeModule_quasiIso R C D M X n p q Z
  simp only [dgGluingShiftModuleMap, CategoryTheory.Functor.map_comp]
  infer_instance

omit p q in
/-- 元の両圏の前三角性を明示入力に持つ、同じ選択版の quasi-isomorphism 性。 -/
lemma dgGluingChosenShiftModuleMap_quasiIso
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    moduleQuasiIso R G (dgGluingChosenShiftModuleMap R C D M X n hC hD) :=
  dgGluingShiftModuleMap_quasiIso R C D M X n
    (dgGluingChooseShiftRepresentative R C X.left n hC)
    (dgGluingChooseShiftRepresentative R D X.right n hD)

end SerrePositivity.InfinityCategories
