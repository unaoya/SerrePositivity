module
public import SerrePositivity.DifferentialGraded.Tensor.GradedSplit
public import SerrePositivity.DifferentialGraded.Tensor.SphereFreeKFlat
public import SerrePositivity.DifferentialGraded.Module.Semifree.Resolution

/-! # 非有界semifree dg加群の相対K-flat性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- semifree filtrationの各段階は相対K-flat。 -/
lemma ModuleSemifreeFiltration.relativeKFlat_stage {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (F.stage n)) := by
  induction n with
  | zero => exact sphereFreePresentation_relativeKFlat A D F.initial
  | succ n ih =>
    exact moduleRelativeKFlat_of_gradedSplit A D (F.split n) ih
      (sphereFreePresentation_relativeKFlat A D (F.quotientPresentation n))

/-- 網羅的filtrationの実際の余極限から相対K-flat性を得る。 -/
lemma ModuleSemifreeFiltration.relativeKFlat {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  have hc := moduleRelativeKFlat_sequentialColimit A D (Functor.ofSequence F.transition)
    (fun n => F.relativeKFlat_stage A D n)
  let e : colimit (Functor.ofSequence F.transition) ≅ M :=
    (colimit.isColimit _).coconePointUniqueUpToIso F.isColimit ≪≫ F.iso
  exact moduleRelativeKFlat_of_iso A D e.symm hc

/-- 任意可換環・非有界dg加群のsemifree性は相対K-flat性を含意する。 -/
lemma moduleSemifree_relativeKFlat {M : ModuleCategory A D} (h : moduleSemifree A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  obtain ⟨F⟩ := h
  exact F.relativeKFlat A D

/-- 任意dg加群の既存semifree解像度は相対K-flat解像度にもなる。 -/
theorem exists_relativeKFlat_resolution (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P) ∧
        moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q := by
  obtain ⟨P, q, hP, hs, hq⟩ := exists_semifree_resolution A D M
  exact ⟨P, q, hP, moduleSemifree_relativeKFlat A D hP, hs, hq⟩

end SerrePositivity.DifferentialGraded
