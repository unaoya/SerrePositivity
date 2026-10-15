module
public import SerrePositivity.DifferentialGraded.Module.ResolutionSequence
public import SerrePositivity.DifferentialGraded.Complexes.FilteredCycles

/-! # 可算cell候補からの射の準同型性

全kernel cycleを有限段へ持ち上げ、一段階後で消す。semifree filtrationは別途構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleResolutionCandidate_cycle_rep (M : ModuleCategory A D) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)) n) :
    ∃ (k : ℕ) (t : complexCycles A ((moduleEvaluation A D x).obj
      (moduleResolutionStage A D M k).left) n),
      ((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n t.val = z.val := by
  exact complexSequentialColimit_cycle_rep A
    (moduleResolutionDiagram A D M ⋙ moduleEvaluation A D x)
    ((moduleEvaluation A D x).mapCocone (colimit.cocone (moduleResolutionDiagram A D M)))
    (isColimitOfPreserves (moduleEvaluation A D x) (colimit.isColimit _)) n z

lemma moduleResolutionCandidate_kernelCycle_boundary (M : ModuleCategory A D) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)) (n + 1))
    (hz : ((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).X n,
      ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).d n (n + 1) t = z.val ∧
      ((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f n t = 0 := by
  obtain ⟨k, c, hc⟩ := moduleResolutionCandidate_cycle_rep A D M x (n + 1) z
  have hkc : ((moduleEvaluation A D x).map (moduleResolutionStage A D M k).hom).f
      (n + 1) c.val = 0 := by
    have h := congrArg (fun f => ((moduleEvaluation A D x).map f).f (n + 1) c.val)
      (moduleResolutionCandidateι_π A D M k)
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
    exact h.symm.trans ((congrArg
      (((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f (n + 1)) hc).trans hz)
  obtain ⟨t, ht, hq⟩ := moduleResolutionCandidate_killsStage A D M k x n c hkc
  exact ⟨t, ht.trans hc, hq⟩

lemma moduleResolutionCandidate_boundaryLift (M : ModuleCategory A D) (x : D) (n : ℤ) :
    moduleBoundaryLiftAt A D x n (moduleResolutionCandidateπ A D M) := by
  intro z y hzy
  let K := (moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)
  let L := (moduleEvaluation A D x).obj M
  let f := (moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)
  obtain ⟨t, ht⟩ := moduleResolutionCandidateπ_degreewiseSurjective A D M x n y
  have hd : K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) t) = 0 :=
    congrArg (fun a => a t) (K.d_comp_d n (n + 1) (n + 1 + 1))
  let c : complexCycles A K (n + 1) := ⟨z.val - K.d n (n + 1) t, by
    change K.d (n + 1) (n + 1 + 1) (z.val - K.d n (n + 1) t) = 0
    rw [map_sub, z.property, hd, sub_self]⟩
  have hc : f.f (n + 1) c.val = 0 := by
    have h := congrArg (fun a => a t) (f.comm n (n + 1))
    change L.d n (n + 1) (f.f n t) = f.f (n + 1) (K.d n (n + 1) t) at h
    change f.f (n + 1) (z.val - K.d n (n + 1) t) = 0
    rw [map_sub, ← h, ht, hzy, sub_self]
  obtain ⟨w, hw, hq⟩ := moduleResolutionCandidate_kernelCycle_boundary A D M x n c hc
  refine ⟨t + w, ?_, ?_⟩
  · change K.d n (n + 1) (t + w) = z.val
    rw [map_add, hw]
    change K.d n (n + 1) t + (z.val - K.d n (n + 1) t) = z.val
    exact (add_comm (K.d n (n + 1) t) (z.val - K.d n (n + 1) t)).trans
      (sub_add_cancel _ _)
  · change f.f n (t + w) = y
    rw [map_add, ht, hq, add_zero]

/-- 可算cell付加の余極限から元の加群への射は指定objectwise quasiIso。 -/
lemma moduleResolutionCandidateπ_quasiIso (M : ModuleCategory A D) :
    moduleQuasiIso A D (moduleResolutionCandidateπ A D M) :=
  moduleQuasiIso_of_boundary_lifting A D _ (moduleResolutionCandidate_boundaryLift A D M)

end SerrePositivity.DifferentialGraded
