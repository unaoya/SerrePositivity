module
public import SerrePositivity.DifferentialGraded.Module.Semifree.Basic
public import SerrePositivity.DifferentialGraded.Module.ResolutionFreeQuotients
public import SerrePositivity.DifferentialGraded.Module.DiskCoverFiltration

/-! # 任意dg加群のsemifree解像度

初期sphere段を既存の可算cell列の前に加え、その余極限が既存候補であることを証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleSemifreeResolutionStage (M : ModuleCategory A D) : ℕ → ModuleCategory A D
  | 0 => ∐ moduleDiskCoverUpperFamily A D M
  | k + 1 => (moduleResolutionStage A D M k).left

def moduleSemifreeResolutionTransition (M : ModuleCategory A D) (k : ℕ) :
    moduleSemifreeResolutionStage A D M k ⟶ moduleSemifreeResolutionStage A D M (k + 1) :=
  match k with
  | 0 => moduleDiskCoverBoundary A D M
  | k + 1 => (moduleResolutionTransition A D M k).left

def moduleSemifreeResolutionDiagram (M : ModuleCategory A D) : ℕ ⥤ ModuleCategory A D :=
  Functor.ofSequence (moduleSemifreeResolutionTransition A D M)

/-- refined列へのcoconeを、既存列のtail coconeへ制限する。 -/
def moduleSemifreeResolutionTailCocone (M : ModuleCategory A D)
    (c : Cocone (moduleSemifreeResolutionDiagram A D M)) :
    Cocone (moduleResolutionDiagram A D M) where
  pt := c.pt
  ι := NatTrans.ofSequence (fun k => c.ι.app (k + 1)) (by
    intro k
    have h := c.w (homOfLE (Nat.le_succ (k + 1)))
    simp only [moduleSemifreeResolutionDiagram, Functor.ofSequence_map_homOfLE_succ] at h
    change (moduleResolutionTransition A D M k).left ≫ c.ι.app (k + 1 + 1) =
      c.ι.app (k + 1) at h
    change (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_succ k)) ≫
      c.ι.app (k + 1 + 1) = c.ι.app (k + 1) ≫ 𝟙 _
    simpa only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
      moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ, Category.comp_id] using h)

def moduleSemifreeResolutionCocone (M : ModuleCategory A D) :
    Cocone (moduleSemifreeResolutionDiagram A D M) where
  pt := moduleResolutionCandidate A D M
  ι := NatTrans.ofSequence
    (fun k => match k with
      | 0 => moduleDiskCoverBoundary A D M ≫ moduleResolutionCandidateι A D M 0
      | k + 1 => moduleResolutionCandidateι A D M k) (by
        intro k
        cases k with
        | zero =>
          simp only [moduleSemifreeResolutionDiagram,
            Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
          exact (Category.comp_id _).symm
        | succ k =>
          simp only [moduleSemifreeResolutionDiagram,
            Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
          exact (moduleResolutionCandidateι_succ A D M k).trans (Category.comp_id _).symm)

/-- 初期段を一段追加しても、既存の余極限候補が余極限である。 -/
def moduleSemifreeResolutionIsColimit (M : ModuleCategory A D) :
    IsColimit (moduleSemifreeResolutionCocone A D M) where
  desc c := colimit.desc _ (moduleSemifreeResolutionTailCocone A D M c)
  fac c k := by
    cases k with
    | zero =>
      change (moduleDiskCoverBoundary A D M ≫ moduleResolutionCandidateι A D M 0) ≫
        colimit.desc _ (moduleSemifreeResolutionTailCocone A D M c) = c.ι.app 0
      have hf : moduleResolutionCandidateι A D M 0 ≫
          colimit.desc _ (moduleSemifreeResolutionTailCocone A D M c) = c.ι.app 1 :=
        colimit.ι_desc (moduleSemifreeResolutionTailCocone A D M c) 0
      have h := c.w (homOfLE (Nat.le_succ 0))
      have h0 : moduleDiskCoverBoundary A D M ≫ c.ι.app 1 = c.ι.app 0 := by
        simp only [moduleSemifreeResolutionDiagram,
          Functor.ofSequence_map_homOfLE_succ] at h
        change moduleDiskCoverBoundary A D M ≫ c.ι.app 1 = c.ι.app 0 at h
        exact h
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun b => moduleDiskCoverBoundary A D M ≫ b) hf).trans h0)
    | succ k => exact colimit.ι_desc (moduleSemifreeResolutionTailCocone A D M c) k
  uniq c b h := by
    apply colimit.hom_ext (F := moduleResolutionDiagram A D M)
    intro k
    exact (h (k + 1)).trans (colimit.ι_desc (moduleSemifreeResolutionTailCocone A D M c) k).symm

def moduleSemifreeResolutionQuotient (M : ModuleCategory A D) : ℕ → ModuleCategory A D
  | 0 => ∐ moduleDiskCoverLowerFamily A D M
  | k + 1 => (moduleKernelCellSource A D (moduleResolutionStage A D M k).hom)⟦(1 : ℤ)⟧

def moduleSemifreeResolutionQuotientMap (M : ModuleCategory A D) (k : ℕ) :
    moduleSemifreeResolutionStage A D M (k + 1) ⟶ moduleSemifreeResolutionQuotient A D M k :=
  match k with
  | 0 => moduleDiskCoverQuotient A D M
  | k + 1 => moduleKernelCellStepQuotient A D (moduleResolutionStage A D M k).hom

def moduleSemifreeResolutionSplit (M : ModuleCategory A D) (k : ℕ) :
    ModuleGradedSplit A D (moduleSemifreeResolutionTransition A D M k)
      (moduleSemifreeResolutionQuotientMap A D M k) :=
  match k with
  | 0 => moduleDiskCoverGradedSplit A D M
  | k + 1 => moduleKernelCellStepGradedSplit A D (moduleResolutionStage A D M k).hom

def moduleSemifreeResolutionInitial (M : ModuleCategory A D) :
    ModuleSphereFreePresentation A D (moduleSemifreeResolutionStage A D M 0) where
  Index := ModuleDiskCoverIndex A D M
  object := fun t => t.1
  degree := fun t => t.2.1 + 1
  iso := Iso.refl _

def moduleSemifreeResolutionQuotientPresentation (M : ModuleCategory A D) (k : ℕ) :
    ModuleSphereFreePresentation A D (moduleSemifreeResolutionQuotient A D M k) := by
  cases k with
  | zero => exact
      { Index := ModuleDiskCoverIndex A D M
        object := fun t => t.1
        degree := fun t => t.2.1
        iso := Iso.refl _ }
  | succ k => exact
      { Index := ModuleKernelCellIndex A D (moduleResolutionStage A D M k).hom
        object := fun t => t.1
        degree := fun t => t.2.1
        iso := moduleKernelCellQuotientFreeIso A D (moduleResolutionStage A D M k).hom }

/-- 既存の可算cell候補の、実際のsemifree filtration。 -/
def moduleResolutionSemifreeFiltration (M : ModuleCategory A D) :
    ModuleSemifreeFiltration A D (moduleResolutionCandidate A D M) where
  stage := moduleSemifreeResolutionStage A D M
  transition := moduleSemifreeResolutionTransition A D M
  initial := moduleSemifreeResolutionInitial A D M
  quotient := moduleSemifreeResolutionQuotient A D M
  quotientMap := moduleSemifreeResolutionQuotientMap A D M
  split := moduleSemifreeResolutionSplit A D M
  quotientPresentation := moduleSemifreeResolutionQuotientPresentation A D M
  cocone := moduleSemifreeResolutionCocone A D M
  isColimit := moduleSemifreeResolutionIsColimit A D M
  iso := Iso.refl _

lemma moduleResolutionCandidate_semifree (M : ModuleCategory A D) :
    moduleSemifree A D (moduleResolutionCandidate A D M) :=
  ⟨moduleResolutionSemifreeFiltration A D M⟩

/-- 任意dg加群には、次数ごと全射かつ準同型なsemifree解像度が存在する。 -/
theorem exists_semifree_resolution (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q :=
  ⟨moduleResolutionCandidate A D M, moduleResolutionCandidateπ A D M,
    moduleResolutionCandidate_semifree A D M,
    moduleResolutionCandidateπ_degreewiseSurjective A D M,
    moduleResolutionCandidateπ_quasiIso A D M⟩

end SerrePositivity.DifferentialGraded
