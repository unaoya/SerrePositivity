module
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import Mathlib.Data.ZMod.Basic

/-! # U6c の全次数転置・自由評価随伴の受入検証と公理監査 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory Opposite
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
example (x : D) : freeAt x ⊣ moduleEvaluation A D x := freeEvaluationAdjunction A D x
example (K : Complex A) (M N : RightModule A D) :
    (ForgetEnrichment.of (Complex A) (tensorModule K M) ⟶ ForgetEnrichment.of (Complex A) N) ≃
      ModuleParamTrans A D K M N := tensorClosedHomEquiv A D K M N
example (x : D) (K : Complex A) (M : ModuleCategory A D) :
    ((freeAt x).obj K ⟶ M) ≃ (K ⟶ (moduleEvaluation A D x).obj M) :=
  freeHomEquiv A D x K M
example (x : D) (K : Complex A) :
    (freeAt x).map ((freeEvaluationAdjunction A D x).unit.app K) ≫
      (freeEvaluationAdjunction A D x).counit.app ((freeAt x).obj K) =
    𝟙 ((freeAt x).obj K) := (freeEvaluationAdjunction A D x).left_triangle_components K
example (x : D) (M : ModuleCategory A D) :
    (freeEvaluationAdjunction A D x).unit.app ((moduleEvaluation A D x).obj M) ≫
      (moduleEvaluation A D x).map ((freeEvaluationAdjunction A D x).counit.app M) =
    𝟙 ((moduleEvaluation A D x).obj M) :=
  (freeEvaluationAdjunction A D x).right_triangle_components M
example : freeAt (A := ℤ) PUnit.unit ⊣ moduleEvaluation ℤ PUnit.{1} PUnit.unit :=
  freeEvaluationAdjunction ℤ PUnit.{1} PUnit.unit
example : freeAt (A := ZMod 2) PUnit.unit ⊣
    moduleEvaluation (ZMod 2) PUnit.{1} PUnit.unit :=
  freeEvaluationAdjunction (ZMod 2) PUnit.{1} PUnit.unit
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.moduleMapFamilyEquiv
#print axioms SerrePositivity.DifferentialGraded.closedFamily_action
#print axioms SerrePositivity.DifferentialGraded.closedFamily_of_action
#print axioms SerrePositivity.DifferentialGraded.tensorFamilyCurry
#print axioms SerrePositivity.DifferentialGraded.tensorFamilyUncurry_naturality
#print axioms SerrePositivity.DifferentialGraded.tensorClosedHomEquiv
#print axioms SerrePositivity.DifferentialGraded.freeHomEquiv_naturality_left
#print axioms SerrePositivity.DifferentialGraded.freeHomEquiv_naturality_right
#print axioms SerrePositivity.DifferentialGraded.freeEvaluationAdjunction
