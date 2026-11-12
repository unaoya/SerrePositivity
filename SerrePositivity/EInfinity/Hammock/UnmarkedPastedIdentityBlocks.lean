module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedSelectedBlocks
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagramTransport

/-!
# 元の貼り戻しの内部接続列と恒等列の全図式の比較

概要：左右の実際の接続列を元の生成矢の端点の恒等列へ回収する。
方針：全成分の長さ零と元の接合点関手の等式を一列の図式へ渡す。
規約：恒等射は射列の圏内の長さ零の射である。
使われ方：prefix・残りの恒等列付き図式への照合。
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

lemma leftBlock_identity :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W.paths
        (𝟙 ((Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.left)))
        (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)) := by
  have hB := congrArg (fun t : Quiver.Total C =>
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from t.left))
      (simplex_generator W g σ τ h)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_heq W.paths (selected_sourceJoint_eq W g σ τ h) hB
    _ _ (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)).endpoint_right_mem f)
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zeroNatTrans_heq_id _
      (leftAttachment_length_zero W g σ τ h) hB)

lemma rightBlock_identity :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram.diagram W.paths
        (𝟙 ((Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.right)))
        (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)) := by
  have hA := congrArg (fun t : Quiver.Total C =>
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from t.right))
      (simplex_generator W g σ τ h)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_heq W.paths hA (selected_targetJoint_eq W g σ τ h)
    _ _ (fun _ => W.paths.id_mem _)
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)).endpoint_left_mem f)
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zeroNatTrans_heq_id _
      (rightAttachment_length_zero W g σ τ h) (selected_targetJoint_eq W g σ τ h))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
