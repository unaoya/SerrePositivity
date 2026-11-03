module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10a13：任意非有界dg加群へのsemifree解像度の存在 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q :=
  exists_semifree_resolution A D M
example (M : ModuleCategory A D) :
    ModuleSemifreeFiltration A D (moduleResolutionCandidate A D M) :=
  moduleResolutionSemifreeFiltration A D M
example (M : ModuleCategory A D) :
    IsColimit (moduleSemifreeResolutionCocone A D M) := moduleSemifreeResolutionIsColimit A D M
example {M : ModuleCategory A D} (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    Mono (F.transition n) := (F.split n).mono
example {M : ModuleCategory A D} (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (F.quotientMap n) (F.split n).inclusion_projection) :=
  F.stepCokernel A D n
example (M : ModuleCategory A D) (n : ℕ) :
    ModuleSphereFreePresentation A D (moduleSemifreeResolutionQuotient A D M n) :=
  moduleSemifreeResolutionQuotientPresentation A D M n
example (M : ModuleCategory ℤ PUnit.{1}) :
    ∃ (P : ModuleCategory ℤ PUnit.{1}) (q : P ⟶ M),
      moduleSemifree ℤ PUnit.{1} P ∧ moduleDegreewiseSurjective ℤ PUnit.{1} q ∧
        moduleQuasiIso ℤ PUnit.{1} q := exists_semifree_resolution ℤ PUnit.{1} M
example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    ∃ (P : ModuleCategory (ZMod 2) PUnit.{1}) (q : P ⟶ M),
      moduleSemifree (ZMod 2) PUnit.{1} P ∧ moduleDegreewiseSurjective (ZMod 2) PUnit.{1} q ∧
        moduleQuasiIso (ZMod 2) PUnit.{1} q := exists_semifree_resolution (ZMod 2) PUnit.{1} M
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.ModuleSphereFreePresentation
#print axioms SerrePositivity.DifferentialGraded.ModuleSemifreeFiltration
#print axioms SerrePositivity.DifferentialGraded.moduleSemifree
#print axioms SerrePositivity.DifferentialGraded.ModuleSemifreeFiltration.stepCokernel
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionStage
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionTransition
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionDiagram
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionTailCocone
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionCocone
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionIsColimit
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionQuotient
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionQuotientMap
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionSplit
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionInitial
#print axioms SerrePositivity.DifferentialGraded.moduleSemifreeResolutionQuotientPresentation
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionSemifreeFiltration
#print axioms SerrePositivity.DifferentialGraded.moduleResolutionCandidate_semifree
#print axioms SerrePositivity.DifferentialGraded.exists_semifree_resolution
