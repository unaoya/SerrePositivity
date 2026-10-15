module
public import SerrePositivity.DifferentialGraded.Module.TensorSource

/-! # U10b3b：固定複体とのtensorの余極限保存 -/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example {M N : ModuleCategory A D} (f : M ⟶ N)
    (hf : ∀ x : D, IsIso ((moduleEvaluation A D x).map f)) : IsIso f :=
  moduleIsIso_of_evaluations A D f hf
example {J : Type w} [Category.{w'} J] [Small.{u} J]
    (F : J ⥤ ModuleCategory A D) (c : Cocone F)
    (hc : ∀ x : D, IsColimit ((moduleEvaluation A D x).mapCocone c)) : IsColimit c :=
  moduleIsColimitOfEvaluations A D c hc
example (K : Complex A) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleTensorLeftMap A D K f) =
      𝟙 K ⊗ₘ (moduleEvaluation A D x).map f := moduleTensorLeftMap_eval A D K f x
example (K : Complex A) {J : Type w} [Category.{w'} J] [Small.{u} J]
    (F : J ⥤ ModuleCategory A D) : PreservesColimit F (moduleTensorLeftFunctor A D K) :=
  inferInstance
example (K : Complex A) (M : ℕ → ModuleCategory A D) :
    IsColimit (Cofan.mk ((moduleTensorLeftFunctor A D K).obj (∐ M))
      (fun j => (moduleTensorLeftFunctor A D K).map (Sigma.ι M j))) :=
  isColimitOfHasCoproductOfPreservesColimit (moduleTensorLeftFunctor A D K) M
end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded

#print axioms moduleIsIso_of_evaluations
#print axioms moduleIsColimitOfEvaluations
#print axioms tensorModuleFamilyMap_naturality
#print axioms moduleTensorLeftObj
#print axioms moduleTensorLeftMap
#print axioms moduleTensorLeftMap_eval
#print axioms moduleTensorLeftFunctor
#print axioms moduleTensorLeftEvaluationIso
#print axioms moduleTensorLeftPreservesColimit
