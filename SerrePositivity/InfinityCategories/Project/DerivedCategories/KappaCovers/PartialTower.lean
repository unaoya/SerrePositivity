module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialStage
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-!
概要：依存閉なセル選択から、実 dg 加群の可算 cell 列とその余極限を作る。
方針：各段の cone 右包含をつなぎ、元の標準 resolution への包含を cocone にする。
規約：余極限は主加群圏の既存の strict 余極限を使う。
使われ方：D-8 d の κ-small な各部分 cell 加群。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) (s : Set (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M))
  (hs : ∀ a ∈ s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDependencies R D M a ⊆ s)

abbrev dgKappaPartialResolutionObject (n : ℕ) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n).object

def dgKappaPartialResolutionTransition (n : ℕ) :
    dgKappaPartialResolutionObject R D M s hs n ⟶
      dgKappaPartialResolutionObject R D M s hs (n + 1) :=
  moduleConeInr R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialAttachment R D M s hs
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n))

@[reassoc] lemma dgKappaPartialResolutionTransition_inclusion (n : ℕ) :
    dgKappaPartialResolutionTransition R D M s hs n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs (n + 1)).inclusion =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n).inclusion ≫
          (moduleResolutionTransition R D M n).left :=
  moduleConeMap_inr R D _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaKernelSubsetAttachment_square R D (moduleResolutionStage R D M n).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n).inclusion
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n).degreewiseMono
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialBoundaryLift R D M s hs
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n)))

def dgKappaPartialResolutionDiagram : ℕ ⥤ ModuleCategory R D :=
  Functor.ofSequence (dgKappaPartialResolutionTransition R D M s hs)

def dgKappaPartialResolutionCocone : Cocone (dgKappaPartialResolutionDiagram R D M s hs) where
  pt := moduleResolutionCandidate R D M
  ι := NatTrans.ofSequence (fun n => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n).inclusion ≫
    moduleResolutionCandidateι R D M n) (by
      intro n
      simp only [dgKappaPartialResolutionDiagram, Functor.ofSequence_map_homOfLE_succ,
        Functor.const_obj_map, Category.comp_id]
      rw [dgKappaPartialResolutionTransition_inclusion_assoc,
        moduleResolutionCandidateι_succ]
      exact (Category.comp_id _).symm)

def dgKappaPartialResolution := colimit (dgKappaPartialResolutionDiagram R D M s hs)

def dgKappaPartialResolutionInclusion :
    dgKappaPartialResolution R D M s hs ⟶ moduleResolutionCandidate R D M :=
  colimit.desc _ (dgKappaPartialResolutionCocone R D M s hs)

lemma dgKappaPartialResolutionStageToCandidate_degreewiseMono (n : ℕ) (x : D) (q : ℤ) :
    Mono (((moduleEvaluation R D x).map
      ((dgKappaPartialResolutionCocone R D M s hs).ι.app n)).f q) := by
  change Mono (((moduleEvaluation R D x).map
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n).inclusion ≫
      moduleResolutionCandidateι R D M n)).f q)
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
  letI := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionPartialStage R D M s hs n).degreewiseMono x q
  letI := moduleResolutionCandidateι_degreewiseMono R D M n x q
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
