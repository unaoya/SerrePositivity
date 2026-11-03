module
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U7b2：shift の零・加法・逆と評価の整合性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : HasShift (ModuleCategory A D) ℤ := inferInstance
example (s : ℤ) : (CategoryTheory.shiftFunctor (ModuleCategory A D) s).Additive := inferInstance
example (x : D) : (moduleEvaluation A D x).CommShift ℤ := inferInstance
example : CategoryTheory.shiftFunctor (ModuleCategory A D) (0 : ℤ) ≅ 𝟭 (ModuleCategory A D) :=
  shiftFunctorZero _ _
example (s t : ℤ) : CategoryTheory.shiftFunctor (ModuleCategory A D) (s + t) ≅
    CategoryTheory.shiftFunctor (ModuleCategory A D) s ⋙
      CategoryTheory.shiftFunctor (ModuleCategory A D) t := shiftFunctorAdd _ _ _
example (s : ℤ) (M : ModuleCategory A D) : (M⟦s⟧)⟦-s⟧ ≅ M :=
  (shiftFunctorCompIsoId (ModuleCategory A D) s (-s) (add_neg_cancel s)).app M
example (s : ℤ) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (M⟦s⟧) ≅ ((moduleEvaluation A D x).obj M)⟦s⟧ :=
  ((moduleEvaluation A D x).commShiftIso s).app M
example (s t : ℤ) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((shiftFunctorAdd (ModuleCategory A D) s t).hom.app M) =
      (shiftFunctorAdd (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftAddIso_hom_eval A D s t M x
example (M : ModuleCategory ℤ PUnit.{1}) :
    (moduleEvaluation ℤ PUnit.{1} PUnit.unit).obj (M⟦(-1 : ℤ)⟧) ≅
      ((moduleEvaluation ℤ PUnit.{1} PUnit.unit).obj M)⟦(-1 : ℤ)⟧ := by
  simpa only [Functor.comp_obj] using
    (((moduleEvaluation ℤ PUnit.{1} PUnit.unit).commShiftIso (-1 : ℤ)).app M)
example : HasShift (ModuleCategory (ZMod 2) PUnit.{1}) ℤ := inferInstance
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.moduleIsoFamily_inv_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleIsoMk
#print axioms SerrePositivity.DifferentialGraded.moduleIsoMk_hom_eval
#print axioms SerrePositivity.DifferentialGraded.moduleIsoMk_inv_eval
#print axioms SerrePositivity.DifferentialGraded.homogeneous_XIsoOfEq_hom_comp
#print axioms SerrePositivity.DifferentialGraded.shiftHom_zero_naturality
#print axioms SerrePositivity.DifferentialGraded.shiftHom_add_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj
#print axioms SerrePositivity.DifferentialGraded.moduleShiftAddIsoObj
#print axioms SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj_hom_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftZeroIsoObj_inv_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftAddIsoObj_hom_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftAddIsoObj_inv_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftZeroIso
#print axioms SerrePositivity.DifferentialGraded.moduleShiftAddIso
#print axioms SerrePositivity.DifferentialGraded.moduleShiftFunctor_map_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftZeroIso_hom_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftZeroIso_inv_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftAddIso_hom_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftAddIso_inv_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftMkCore
#print axioms SerrePositivity.DifferentialGraded.moduleHasShift
#print axioms SerrePositivity.DifferentialGraded.moduleShiftFunctor_eq
#print axioms SerrePositivity.DifferentialGraded.moduleShiftZero_eq
#print axioms SerrePositivity.DifferentialGraded.moduleShiftAdd_eq
#print axioms SerrePositivity.DifferentialGraded.moduleShiftFunctorAdditive
#print axioms SerrePositivity.DifferentialGraded.moduleShiftAdditive
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationCommShift
