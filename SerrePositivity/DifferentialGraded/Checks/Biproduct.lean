module
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U7a2：有限直和の全次数作用・普遍性・評価の受入と公理監査 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : HasFiniteBiproducts (ModuleCategory A D) := inferInstance
example (M N : ModuleCategory A D) : (moduleBinaryBicone A D M N).IsBilimit :=
  moduleBinaryBiconeIsBilimit A D M N
example (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (moduleBiprod A D M N) =
      ((moduleEvaluation A D x).obj M ⊞ (moduleEvaluation A D x).obj N) := rfl
example (M N : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (M ⊞ N) ≅
      (moduleEvaluation A D x).obj M ⊞ (moduleEvaluation A D x).obj N :=
  moduleEvaluationBiprodIso A D M N x
example (J : Type) [Finite J] (M : J → ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (⨁ M) ≅ ⨁ (fun j => (moduleEvaluation A D x).obj (M j)) :=
  (moduleEvaluation A D x).mapBiproduct M
example (M N : ModuleCategory ℤ PUnit.{1}) :
    (moduleEvaluation ℤ PUnit.{1} PUnit.unit).obj (M ⊞ N) ≅
      (moduleEvaluation ℤ PUnit.{1} PUnit.unit).obj M ⊞
        (moduleEvaluation ℤ PUnit.{1} PUnit.unit).obj N :=
  moduleEvaluationBiprodIso _ _ _ _ _
example : HasFiniteBiproducts (ModuleCategory (ZMod 2) PUnit.{1}) := inferInstance
example (M N : RightModule A D) (x y : Dᵒᵖ) (i : ℤ)
    (f : GradedHom A x y (-1)) :
    (((biprodModule M N).map x y).f (-1) f).v i (i - 1) (by omega) =
      (biprod.fst : M.obj x ⊞ N.obj x ⟶ M.obj x).f i ≫
        ((M.map x y).f (-1) f).v i (i - 1) (by omega) ≫
          (biprod.inl : M.obj y ⟶ M.obj y ⊞ N.obj y).f (i - 1) +
      (biprod.snd : M.obj x ⊞ N.obj x ⟶ N.obj x).f i ≫
        ((N.map x y).f (-1) f).v i (i - 1) (by omega) ≫
          (biprod.inr : N.obj y ⟶ M.obj y ⊞ N.obj y).f (i - 1) :=
  biprodModule_map_v M N x y _ _ _ _ f
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap_precomp
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap_v
#print axioms SerrePositivity.DifferentialGraded.homComplex_biprod_ext
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap_identity
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap_fst
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap_snd
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap_inl
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap_inr
#print axioms SerrePositivity.DifferentialGraded.biprodHomMap_comp
#print axioms SerrePositivity.DifferentialGraded.biprodModule
#print axioms SerrePositivity.DifferentialGraded.biprodModule_map_v
#print axioms SerrePositivity.DifferentialGraded.moduleBiprod
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodFst
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodSnd
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodInl
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodInr
#print axioms SerrePositivity.DifferentialGraded.moduleBinaryBicone
#print axioms SerrePositivity.DifferentialGraded.moduleBinaryBicone_total
#print axioms SerrePositivity.DifferentialGraded.moduleBinaryBiconeIsBilimit
#print axioms SerrePositivity.DifferentialGraded.moduleHasBinaryBiproducts
#print axioms SerrePositivity.DifferentialGraded.moduleHasFiniteBiproducts
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodIso
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationBiprodIso
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodFst_eval
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodSnd_eval
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodInl_eval
#print axioms SerrePositivity.DifferentialGraded.moduleBiprodInr_eval
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationPreservesBinaryBiproducts
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationBiprodIso_fst
#print axioms SerrePositivity.DifferentialGraded.moduleEvaluationBiprodIso_snd
