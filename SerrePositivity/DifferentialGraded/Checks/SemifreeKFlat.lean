module
public import SerrePositivity.DifferentialGraded.Tensor.Semifree
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # semifree相対K-flat解像度の任意環・独立宇宙での受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M : ModuleCategory A D) (F : ModuleSemifreeFiltration A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) :=
  F.relativeKFlat A D

example (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P) ∧
        moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q :=
  exists_relativeKFlat_resolution A D M

example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    ∃ (P : ModuleCategory (ZMod 2) PUnit.{1}) (q : P ⟶ M),
      moduleSemifree (ZMod 2) PUnit.{1} P ∧
        moduleRelativeKFlat (ZMod 2) PUnit.{1} (ForgetEnrichment.to (Complex (ZMod 2)) P) ∧
        moduleDegreewiseSurjective (ZMod 2) PUnit.{1} q ∧ moduleQuasiIso (ZMod 2) PUnit.{1} q :=
  exists_relativeKFlat_resolution (ZMod 2) PUnit.{1} M

#print axioms ModuleSemifreeFiltration.relativeKFlat_stage
#print axioms ModuleSemifreeFiltration.relativeKFlat
#print axioms moduleSemifree_relativeKFlat
#print axioms exists_relativeKFlat_resolution
