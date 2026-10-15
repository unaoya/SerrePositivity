module
public import SerrePositivity.DifferentialGraded.Module.KernelCells
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # kernelのcycleを順に消す可算cell列

自由disk被覆から始め、各段階で前段のkernelの全cycleを消す。
このファイルの余極限は解像度の候補であり、準同型性とsemifree性は別途証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleResolutionStage (M : ModuleCategory A D) : ℕ → Over M
  | 0 => Over.mk (moduleDiskCoverπ A D M)
  | n + 1 => Over.mk (moduleKernelCellStepπ A D (moduleResolutionStage M n).hom)

def moduleResolutionTransition (M : ModuleCategory A D) (n : ℕ) :
    moduleResolutionStage A D M n ⟶ moduleResolutionStage A D M (n + 1) :=
  Over.homMk (moduleKernelCellStepι A D (moduleResolutionStage A D M n).hom)
    (moduleKernelCellStep_fac A D _)

lemma moduleResolutionStage_degreewiseSurjective (M : ModuleCategory A D) (n : ℕ) :
    moduleDegreewiseSurjective A D (moduleResolutionStage A D M n).hom := by
  induction n with
  | zero => exact moduleDiskCoverπ_degreewiseSurjective A D M
  | succ n hn => exact moduleKernelCellStepπ_degreewiseSurjective A D _ hn

def moduleResolutionOverDiagram (M : ModuleCategory A D) : ℕ ⥤ Over M :=
  Functor.ofSequence (moduleResolutionTransition A D M)

def moduleResolutionDiagram (M : ModuleCategory A D) : ℕ ⥤ ModuleCategory A D :=
  moduleResolutionOverDiagram A D M ⋙ Over.forget M

def moduleResolutionCocone (M : ModuleCategory A D) : Cocone (moduleResolutionDiagram A D M) where
  pt := M
  ι :=
    { app n := (moduleResolutionStage A D M n).hom
      naturality i j f := by
        change ((moduleResolutionOverDiagram A D M).map f).left ≫
          (moduleResolutionStage A D M j).hom = (moduleResolutionStage A D M i).hom ≫ 𝟙 M
        rw [Category.comp_id]
        exact Over.w _ }

/-- 可算cell列の余極限。準同型・semifree性の証明前の候補。 -/
def moduleResolutionCandidate (M : ModuleCategory A D) : ModuleCategory A D :=
  colimit (moduleResolutionDiagram A D M)

def moduleResolutionCandidateπ (M : ModuleCategory A D) : moduleResolutionCandidate A D M ⟶ M :=
  colimit.desc _ (moduleResolutionCocone A D M)

def moduleResolutionCandidateι (M : ModuleCategory A D) (n : ℕ) :
    (moduleResolutionStage A D M n).left ⟶ moduleResolutionCandidate A D M :=
  colimit.ι (moduleResolutionDiagram A D M) n

@[reassoc] lemma moduleResolutionCandidateι_π (M : ModuleCategory A D) (n : ℕ) :
    moduleResolutionCandidateι A D M n ≫ moduleResolutionCandidateπ A D M =
      (moduleResolutionStage A D M n).hom :=
  colimit.ι_desc (moduleResolutionCocone A D M) n

@[reassoc] lemma moduleResolutionCandidateι_succ (M : ModuleCategory A D) (n : ℕ) :
    (moduleResolutionTransition A D M n).left ≫ moduleResolutionCandidateι A D M (n + 1) =
      moduleResolutionCandidateι A D M n := by
  have h := colimit.w (moduleResolutionDiagram A D M) (homOfLE (Nat.le_succ n))
  have hm : (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_succ n)) =
      (moduleResolutionTransition A D M n).left := by
    simp only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
      moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ]
  change (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_succ n)) ≫
    moduleResolutionCandidateι A D M (n + 1) = moduleResolutionCandidateι A D M n at h
  rw [hm] at h
  exact h

lemma moduleResolutionCandidateπ_degreewiseSurjective (M : ModuleCategory A D) :
    moduleDegreewiseSurjective A D (moduleResolutionCandidateπ A D M) := by
  intro x n y
  obtain ⟨t, ht⟩ := moduleResolutionStage_degreewiseSurjective A D M 0 x n y
  refine ⟨((moduleEvaluation A D x).map (colimit.ι (moduleResolutionDiagram A D M) 0)).f n t, ?_⟩
  have h := congrArg (fun k => ((moduleEvaluation A D x).map k).f n t)
    (colimit.ι_desc (moduleResolutionCocone A D M) 0)
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
  exact h.trans ht

/-- 有限段のkernel内のcycleは、最終候補でkernel内の境界になる。 -/
lemma moduleResolutionCandidate_killsStage (M : ModuleCategory A D) (k : ℕ) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj
      (moduleResolutionStage A D M k).left) (n + 1))
    (hz : ((moduleEvaluation A D x).map (moduleResolutionStage A D M k).hom).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).X n,
      ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).d n (n + 1) t =
        ((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f (n + 1) z.val ∧
      ((moduleEvaluation A D x).map (moduleResolutionCandidateπ A D M)).f n t = 0 := by
  obtain ⟨t, ht, hq⟩ := moduleKernelCellStep_killsInKernel A D
    (moduleResolutionStage A D M k).hom x n z hz
  let i := (moduleEvaluation A D x).map (moduleResolutionCandidateι A D M (k + 1))
  refine ⟨i.f n t, ?_, ?_⟩
  · have h := congrArg (fun f => ((moduleEvaluation A D x).map f).f (n + 1) z.val)
      (moduleResolutionCandidateι_succ A D M k)
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
    have hd := congrArg (fun f => f t) (i.comm n (n + 1))
    exact hd.trans ((congrArg (i.f (n + 1)) ht).trans h)
  · have h := congrArg (fun f => ((moduleEvaluation A D x).map f).f n t)
      (moduleResolutionCandidateι_π A D M (k + 1))
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
    exact h.trans hq

end SerrePositivity.DifferentialGraded
