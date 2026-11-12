module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InverseAttachmentRestriction

/-!
概要：辺反転の貼合せからの元の制限は、任意の単射の相対図式を充填する。
方針：各指定辺で可逆区間の相対延長を選び、全族を余積と pushout で貼る。
規約：元の反転関手族と部分図式を厳密に保持。使われ方：一般局所化の普遍性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

lemma inverseAttachmentRestriction_lifting {A B X Y : SSet.{u}} [Quasicategory Y]
    (W : Set (X _⦋1⦌)) (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (inverseAttachmentRestriction X W Y) := by
  constructor
  intro u v sq
  have : HasLiftingProperty i (walkingEquivalenceRestriction Y) :=
    walkingEquivalenceRestriction_lifting i
  have hs (w : W) : CommSq (u ≫ (pre (inverseAttachmentInterval X W w)).app Y) i
      (walkingEquivalenceRestriction Y) (v ≫ invertingEdgeRestriction X W Y w) := by
    constructor
    rw [Category.assoc, ← inverseAttachmentRestriction_interval, ← Category.assoc, sq.w,
      Category.assoc]
  let l (w : W) := (hs w).lift
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coproductFamilyGlue l
  let f := v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι
  have hfg : f ≫ (pre (markedEdgeEvaluation X W)).app Y =
      g ≫ (pre (inverseIntervalAttachment X W)).app Y := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coproductFamily_hom_ext
    intro w
    have ht := congrArg (fun m => m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) (hs w).fac_right
    rw [Category.assoc, walkingEquivalenceRestriction_ι, Category.assoc,
      invertingEdgeRestriction_ι] at ht
    change l w ≫ (pre walkingEquivalenceEdge).app Y =
      f ≫ (pre (SSet.yonedaEquiv.symm w.val)).app Y at ht
    dsimp only [g]
    simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
      markedEdgeEvaluation_ι, inverseIntervalAttachment_ι]
    rw [pre_map, NatTrans.comp_app, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coproductFamilyGlue_restrict]
    exact ht.symm
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue (markedEdgeEvaluation X W) (inverseIntervalAttachment X W) f g hfg
  have hl : i ≫ r = u := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamily_hom_ext (markedEdgeEvaluation X W) (inverseIntervalAttachment X W)
    · rw [Category.assoc]
      change i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue _ _ f g hfg ≫ (pre (pushout.inl _ _)).app Y) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue_inl]
      have h := congrArg (fun m => m ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι) sq.w
      rw [Category.assoc, inverseAttachmentRestriction_ι, Category.assoc] at h
      exact h.symm
    · rw [Category.assoc]
      change i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue _ _ f g hfg ≫ (pre (pushout.inr _ _)).app Y) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue_inr]
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coproductFamily_hom_ext
      intro w
      rw [Category.assoc]
      change i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coproductFamilyGlue l ≫ (pre (Sigma.ι _ w)).app Y) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coproductFamilyGlue_restrict]
      have h := (hs w).fac_left
      change i ≫ l w = _ at h
      rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
      exact h
  have hr : r ≫ inverseAttachmentRestriction X W Y = v := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι).mp
    rw [Category.assoc, inverseAttachmentRestriction_ι]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue_inl _ _ f g hfg
  exact CommSq.HasLift.mk' { l := r, fac_left := hl, fac_right := hr }

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
