module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedIdentityBlocks
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendWordEndpoints

/-!
# 元の貼り戻しの prefix・残りと恒等列を挿入した全図式

概要：実際の切断結果を元の前後の全図式と恒等列の連結へ照合する。
方針：語・全端点関手・各ブロックの異種等式を連結へ渡す。
規約：元の選択位置と全縦射を保持する。
使われ方：元の標準射と合成単位則による二因子の点の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((simplex W g σ τ).obj 0) j ≠ [])

lemma prefix_identity_diagram :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor ((AllMarked.graphMap W X g.val.left a).app n σ)).append
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W.paths
          (𝟙 ((Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.left)))
          (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _))) := by
  have hw := (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b))
      (simplex_firstColumn W g σ τ h)).trans (before_word a b)
  have hg := congrArg (fun t : Quiver.Total C =>
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from t.left))
      (simplex_generator W g σ τ h)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_heq_word_endpoints hw rfl rfl
    (selected_sourceJoint_eq W g σ τ h) hg (selected_before_diagram W g σ τ h)
      (leftBlock_identity W g σ τ h)

lemma residual_identity_diagram :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W.paths
        (𝟙 ((Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.right)))
        (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)).append
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)) := by
  have hw := (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b))
      (simplex_firstColumn W g σ τ h)).trans (after_word a b)
  have hg := congrArg (fun t : Quiver.Total C =>
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from t.right))
      (simplex_generator W g σ τ h)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_heq_word_endpoints rfl hw hg
    (selected_targetJoint_eq W g σ τ h) rfl (rightBlock_identity W g σ τ h)
      (selected_after_diagram W g σ τ h)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
