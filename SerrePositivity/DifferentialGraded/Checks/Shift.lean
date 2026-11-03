module
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U7b1：整数 shift の全次数符号と評価の受入 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (s : ℤ) (M : RightModule A D) (x : Dᵒᵖ) :
    (shiftModule s M).obj x = (M.obj x)⟦s⟧ := rfl
example (s : ℤ) (x : D) :
    moduleShiftFunctor A D s ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A D x ⋙ CategoryTheory.shiftFunctor (Complex A) s :=
  moduleShiftEvaluationIso A D s x
example (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftMap A D s f) =
      ((moduleEvaluation A D x).map f)⟦s⟧' := moduleShiftMap_eval A D s f x
example (P Q : Complex A) (f : Homogeneous P Q 1) (i : ℤ) :
    ((shiftHom 1 P Q).f 1 f).v i (i + 1) rfl =
      -f.v (i + 1) (i + 1 + 1) (by omega) := by
  rw [shiftHom_v]
  simp only [one_mul, Int.negOnePow_one, Units.neg_smul, one_smul]
example (P Q : Complex A) (f : Homogeneous P Q (-1)) (i : ℤ) :
    ((shiftHom (-1) P Q).f (-1) f).v i (i - 1) (by omega) =
      -f.v (i + (-1)) (i - 1 + (-1)) (by omega) := by
  rw [shiftHom_v]
  norm_num only [Int.negOnePow_one, Units.neg_smul, one_smul]
example {P Q : Complex A} (f : P ⟶ Q) (s : ℤ) :
    (shiftHom s P Q).f 0 (Cochain.ofHom f) = Cochain.ofHom (f⟦s⟧') :=
  shiftHom_ofHom s f
example (s : ℤ) (x : PUnit.{1}) :
    moduleShiftFunctor ℤ PUnit.{1} s ⋙ moduleEvaluation ℤ PUnit.{1} x ≅
      moduleEvaluation ℤ PUnit.{1} x ⋙ CategoryTheory.shiftFunctor (Complex ℤ) s :=
  moduleShiftEvaluationIso _ _ _ _
example (M : RightModule (ZMod 2) PUnit.{1}) :
    (shiftModule (-1) M).obj (op PUnit.unit) = (M.obj (op PUnit.unit))⟦(-1 : ℤ)⟧ := rfl
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.shiftHom
#print axioms SerrePositivity.DifferentialGraded.shiftHom_apply
#print axioms SerrePositivity.DifferentialGraded.shiftHom_v
#print axioms SerrePositivity.DifferentialGraded.shiftHom_ofHom
#print axioms SerrePositivity.DifferentialGraded.shiftHom_identity
#print axioms SerrePositivity.DifferentialGraded.shiftHom_comp
#print axioms SerrePositivity.DifferentialGraded.shiftDG
#print axioms SerrePositivity.DifferentialGraded.shiftModule
#print axioms SerrePositivity.DifferentialGraded.shiftModule_eq_comp
#print axioms SerrePositivity.DifferentialGraded.shiftModule_map_v
#print axioms SerrePositivity.DifferentialGraded.shiftedFamily_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleShiftObj
#print axioms SerrePositivity.DifferentialGraded.moduleShiftMap
#print axioms SerrePositivity.DifferentialGraded.moduleShiftMap_eval
#print axioms SerrePositivity.DifferentialGraded.moduleShiftFunctor
#print axioms SerrePositivity.DifferentialGraded.moduleShiftEvaluationIso
