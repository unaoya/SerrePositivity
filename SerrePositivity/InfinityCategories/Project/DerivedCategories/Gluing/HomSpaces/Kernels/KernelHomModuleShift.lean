module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelHomModules
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.KernelShiftUnits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ModuleShiftGradedIso

/-! 標準 kernel シフトへの制限 Hom 加群を、元の制限 Hom 加群の実シフトと同定する。 -/
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
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomModuleFunctor R C D M
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftObject R C D M X n
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftProjection R C D M X n
local notation "i" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftInclusion R C D M X n

/-- 同じ斉次射影の制限 Yoneda 像は、加群 Hom end 内でも閉じる。 -/
lemma dgGluingKernelHomModuleShift_closed :
    (moduleHom R G ((J).obj S) ((J).obj T)).d n (n + 1) (((J).map S T).f n p) = 0 := by
  have h := congrArg (fun f => f p) (((J).map S T).comm n (n + 1))
  simp only [ModuleCat.comp_apply] at h
  have hp : (S ⟶[Complex R] T).d n (n + 1) p = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftProjection_closed R C D M X n
  rw [hp, map_zero] at h
  exact h

lemma dgGluingKernelHomModuleShift_out_in :
    compose R (((J).map T S).f (-n) i) (((J).map S T).f n p) (add_neg_cancel n) =
      (unitElement R ((J).obj S)).val := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctor_map_compose R J, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftOutIn, (J).map_unitElement R]

lemma dgGluingKernelHomModuleShift_in_out :
    compose R (((J).map S T).f n p) (((J).map T S).f (-n) i) (neg_add_cancel n) =
      (unitElement R ((J).obj T)).val := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctor_map_compose R J, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftInOut, (J).map_unitElement R]

/-- 点ごとの同値に加え、同じ斉次元から得られる全 dg 自然な実加群シフト同型。 -/
def dgGluingKernelHomModuleShiftIso :
    ForgetEnrichment.of (Complex R) ((J).obj S) ≅
      ForgetEnrichment.of (Complex R) (shiftModule n ((J).obj T)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleShiftGradedIso R G ((J).obj S) ((J).obj T) n
    (((J).map S T).f n p) (((J).map T S).f (-n) i)
    (dgGluingKernelHomModuleShift_closed R C D M X n)
    (dgGluingKernelHomModuleShift_out_in R C D M X n)
    (dgGluingKernelHomModuleShift_in_out R C D M X n)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
