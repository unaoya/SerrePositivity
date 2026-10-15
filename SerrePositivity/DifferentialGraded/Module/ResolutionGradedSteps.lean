module
public import SerrePositivity.DifferentialGraded.Module.ConeGradedSplit
public import SerrePositivity.DifferentialGraded.Module.ResolutionQuasiIso

/-! # 可算cell列の各付加の分裂と商

初期disk段のsphereへの分解と自由な商の同定は後続に残す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- kernel cell付加の商への標準射。 -/
def moduleKernelCellStepQuotient {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellStep A D f ⟶ (moduleKernelCellSource A D f)⟦(1 : ℤ)⟧ :=
  moduleConeConnecting A D (moduleKernelCellMap A D f)

def moduleKernelCellStepGradedSplit {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleGradedSplit A D (moduleKernelCellStepι A D f) (moduleKernelCellStepQuotient A D f) :=
  moduleConeGradedSplit A D (moduleKernelCellMap A D f)

lemma moduleKernelCellStepι_mono {M N : ModuleCategory A D} (f : M ⟶ N) :
    Mono (moduleKernelCellStepι A D f) := (moduleKernelCellStepGradedSplit A D f).mono

def moduleKernelCellStepCokernel {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsColimit (CokernelCofork.ofπ (moduleKernelCellStepQuotient A D f)
      (moduleKernelCellStepGradedSplit A D f).inclusion_projection) :=
  moduleGradedSplitCokernel A D (moduleKernelCellStepGradedSplit A D f)

lemma moduleResolutionTransition_mono (M : ModuleCategory A D) (k : ℕ) :
    Mono (moduleResolutionTransition A D M k).left :=
  moduleKernelCellStepι_mono A D (moduleResolutionStage A D M k).hom

/-- 有限段から後の有限段への射はmono。 -/
lemma moduleResolutionDiagram_map_mono (M : ModuleCategory A D) (i j : ℕ) (h : i ≤ j) :
    Mono ((moduleResolutionDiagram A D M).map (homOfLE h)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simpa using (inferInstance : Mono (𝟙 ((moduleResolutionDiagram A D M).obj i)))
  | succ k hk =>
    have he : (moduleResolutionDiagram A D M).map (homOfLE h) =
        (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_add_right i k)) ≫
          (moduleResolutionTransition A D M (i + k)).left := by
      rw [show homOfLE h = homOfLE (Nat.le_add_right i k) ≫ homOfLE (Nat.le_succ (i + k)) from rfl,
        CategoryTheory.Functor.map_comp]
      congr 1
      simp only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
        moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ]
    let : Mono ((moduleResolutionDiagram A D M).map (homOfLE (Nat.le_add_right i k))) := hk _
    let : Mono (moduleResolutionTransition A D M (i + k)).left :=
      moduleResolutionTransition_mono A D M _
    rw [he]
    infer_instance

lemma moduleResolutionDiagram_map_degreewiseMono (M : ModuleCategory A D)
    (x : D) (n : ℤ) (i j : ℕ) (h : i ≤ j) :
    Mono (((moduleEvaluation A D x).map
      ((moduleResolutionDiagram A D M).map (homOfLE h))).f n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp only [homOfLE_refl, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f]; infer_instance
  | succ k hk =>
    have he : (moduleResolutionDiagram A D M).map (homOfLE h) =
        (moduleResolutionDiagram A D M).map (homOfLE (Nat.le_add_right i k)) ≫
          (moduleResolutionTransition A D M (i + k)).left := by
      rw [show homOfLE h = homOfLE (Nat.le_add_right i k) ≫ homOfLE (Nat.le_succ (i + k)) from rfl,
        CategoryTheory.Functor.map_comp]
      congr 1
      simp only [moduleResolutionDiagram, Functor.comp_map, Over.forget_map,
        moduleResolutionOverDiagram, Functor.ofSequence_map_homOfLE_succ]
    let : Mono (((moduleEvaluation A D x).map
      ((moduleResolutionDiagram A D M).map (homOfLE (Nat.le_add_right i k)))).f n) := hk _
    let : Mono (((moduleEvaluation A D x).map
      (moduleResolutionTransition A D M (i + k)).left).f n) :=
      (moduleKernelCellStepGradedSplit A D
        (moduleResolutionStage A D M (i + k)).hom).degreewiseMono x n
    rw [he, CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
    infer_instance

/-- 各有限段の余極限への包含は全評価次数でmono。 -/
lemma moduleResolutionCandidateι_degreewiseMono (M : ModuleCategory A D)
    (k : ℕ) (x : D) (n : ℤ) :
    Mono (((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n
  let F := (moduleResolutionDiagram A D M ⋙ moduleEvaluation A D x) ⋙ ev
  let s := ev.mapCocone ((moduleEvaluation A D x).mapCocone
    (colimit.cocone (moduleResolutionDiagram A D M)))
  have hs : IsColimit s := isColimitOfPreserves ev
    (isColimitOfPreserves (moduleEvaluation A D x) (colimit.isColimit _))
  apply (ModuleCat.mono_iff_injective _).2
  intro a b hab
  obtain ⟨j, f, g, hj⟩ := Concrete.isColimit_exists_of_rep_eq F hs a b hab
  have hfg : g = f := Subsingleton.elim _ _
  rw [hfg] at hj
  have hm : Mono (F.map f) := moduleResolutionDiagram_map_degreewiseMono A D M x n k j (leOfHom f)
  exact (ModuleCat.mono_iff_injective _).1 hm hj

/-- 各有限段は主dg加群圏でも余極限候補へ埋め込まれる。 -/
lemma moduleResolutionCandidateι_mono (M : ModuleCategory A D) (k : ℕ) :
    Mono (moduleResolutionCandidateι A D M k) where
  right_cancellation a b h := by
    apply moduleMorphism_ext
    intro x
    apply HomologicalComplex.Hom.ext
    funext n
    let : Mono (((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n) :=
      moduleResolutionCandidateι_degreewiseMono A D M k x n
    apply (cancel_mono (((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n)).1
    have he := congrArg (fun f => ((moduleEvaluation A D x).map f).f n) h
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using he

/-- 各評価次数の全要素は有限段の像に属する。 -/
lemma moduleResolutionCandidate_element_rep (M : ModuleCategory A D) (x : D) (n : ℤ)
    (z : ((moduleEvaluation A D x).obj (moduleResolutionCandidate A D M)).X n) :
    ∃ (k : ℕ) (t : ((moduleEvaluation A D x).obj (moduleResolutionStage A D M k).left).X n),
      ((moduleEvaluation A D x).map (moduleResolutionCandidateι A D M k)).f n t = z := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n
  exact Concrete.isColimit_exists_rep
    ((moduleResolutionDiagram A D M ⋙ moduleEvaluation A D x) ⋙ ev)
    (isColimitOfPreserves ev
      (isColimitOfPreserves (moduleEvaluation A D x) (colimit.isColimit _))) z

end SerrePositivity.DifferentialGraded
