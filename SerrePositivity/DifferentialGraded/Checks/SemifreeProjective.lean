module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10b5c：semifree全体のHom acyclic性と射影解像度の存在 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M : ModuleCategory A D} (F : ModuleSemifreeFiltration A D M) :
    moduleHomotopicallyProjective A D M := F.homotopicallyProjective A D

example {M : ModuleCategory A D} (hM : moduleSemifree A D M)
    (N : ModuleCategory A D) (hN : moduleAcyclic A D N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).Acyclic :=
  moduleSemifree_homotopicallyProjective A D hM N hN

example (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M), moduleHomotopicallyProjective A D P ∧
      moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q :=
  exists_homotopicallyProjective_resolution A D M

example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    moduleHomotopicallyProjective (ZMod 2) PUnit.{1}
      (moduleResolutionCandidate (ZMod 2) PUnit.{1} M) :=
  moduleSemifree_homotopicallyProjective (ZMod 2) PUnit.{1}
    (moduleResolutionCandidate_semifree (ZMod 2) PUnit.{1} M)

example (F : ℕᵒᵖ ⥤ Complex A) {c : Cone F} (hc : IsLimit c)
    (hF : ∀ n, (F.obj (op n)).Acyclic)
    (hr : ∀ (n : ℕ) (q : ℤ), Function.Surjective
      ((F.map (homOfLE (n.le_add_right 1)).op).f q)) : c.pt.Acyclic :=
  complexTowerLimit_acyclic A F hc hF hr

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms complexLimitDegree_element_ext
#print axioms complexTowerLimit_acyclic
#print axioms ModuleSemifreeFiltration.homotopicallyProjective
#print axioms moduleSemifree_homotopicallyProjective
#print axioms exists_homotopicallyProjective_resolution
