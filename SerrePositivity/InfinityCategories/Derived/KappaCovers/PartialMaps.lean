module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.PartialStageMaps
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.PartialEmbedding

/-!
概要：セル選択の包含に沿う実部分 cell 加群の比較射。
方針：有限段の比較を可算余極限へ延ばし、元への単射で全関手の等式を反映する。
規約：選択した境界持上げの一致は要求せず、包含後の等式を用いる。
使われ方：D-8 d の κ-filtered strict 図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D) (s t : Set (DGKappaResolutionLabel R D M))
  (hs : ∀ a ∈ s, dgKappaResolutionDependencies R D M a ⊆ s)
  (ht : ∀ a ∈ t, dgKappaResolutionDependencies R D M a ⊆ t) (hst : s ⊆ t)

lemma dgKappaPartialStageMap_transition (n : ℕ) :
    dgKappaPartialResolutionTransition R D M s hs n ≫
        (dgKappaPartialStageMap R D M s t hs ht hst (n + 1)).map =
      (dgKappaPartialStageMap R D M s t hs ht hst n).map ≫
        dgKappaPartialResolutionTransition R D M t ht n := by
  let pt := dgKappaResolutionPartialStage R D M t ht (n + 1)
  letI := dgKappaModuleMap_mono R D pt.inclusion pt.degreewiseMono
  apply (cancel_mono pt.inclusion).1
  rw [Category.assoc, (dgKappaPartialStageMap R D M s t hs ht hst (n + 1)).comm,
    dgKappaPartialResolutionTransition_inclusion, Category.assoc,
    dgKappaPartialResolutionTransition_inclusion, ← Category.assoc,
    (dgKappaPartialStageMap R D M s t hs ht hst n).comm]

def dgKappaPartialMapCocone : Cocone (dgKappaPartialResolutionDiagram R D M s hs) where
  pt := dgKappaPartialResolution R D M t ht
  ι := NatTrans.ofSequence
    (fun n => (dgKappaPartialStageMap R D M s t hs ht hst n).map ≫
      colimit.ι (dgKappaPartialResolutionDiagram R D M t ht) n) (by
      intro n
      simp only [dgKappaPartialResolutionDiagram, Functor.ofSequence_map_homOfLE_succ]
      rw [← Category.assoc, dgKappaPartialStageMap_transition, Category.assoc]
      have h := colimit.w (dgKappaPartialResolutionDiagram R D M t ht)
        (homOfLE (Nat.le_succ n))
      simp only [dgKappaPartialResolutionDiagram, Functor.ofSequence_map_homOfLE_succ] at h
      exact (congrArg (fun f => (dgKappaPartialStageMap R D M s t hs ht hst n).map ≫ f) h).trans
        (Category.comp_id _).symm)

def dgKappaPartialResolutionMap :
    dgKappaPartialResolution R D M s hs ⟶ dgKappaPartialResolution R D M t ht :=
  colimit.desc _ (dgKappaPartialMapCocone R D M s t hs ht hst)

@[reassoc] lemma dgKappaPartialResolutionMap_inclusion :
    dgKappaPartialResolutionMap R D M s t hs ht hst ≫
      dgKappaPartialResolutionInclusion R D M t ht =
        dgKappaPartialResolutionInclusion R D M s hs := by
  apply colimit.hom_ext
  intro n
  rw [dgKappaPartialResolutionMap, colimit.ι_desc_assoc]
  change ((dgKappaPartialStageMap R D M s t hs ht hst n).map ≫
    colimit.ι (dgKappaPartialResolutionDiagram R D M t ht) n) ≫
      dgKappaPartialResolutionInclusion R D M t ht = _
  rw [Category.assoc, dgKappaPartialResolutionInclusion, colimit.ι_desc,
    dgKappaPartialResolutionInclusion, colimit.ι_desc]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ moduleResolutionCandidateι R D M n)
      (dgKappaPartialStageMap R D M s t hs ht hst n).comm)

end SerrePositivity.InfinityCategories
