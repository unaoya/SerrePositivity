module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachmentSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagramTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendTransport

/-!
# 内部接続の三つの一列の全図式と全単体作用素

概要：接頭列・生成矢・残りの全一列の図式を元の再添字へ照合する。
方針：生成矢の端点の表示と接続自然変換の異種等式を移す。
規約：全行・全縦射・元の接合点関手を保持する。
使われ方：prefix・残り・refined 全図式の単体的整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma generatorSource_simplex :
    (Functor.const (Fin (m.unop.len + 1))).obj
      (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ).left) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ ⋙ (Functor.const (Fin (n.unop.len + 1))).obj
      (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).left) :=
  congrArg (fun a => (Functor.const (Fin (m.unop.len + 1))).obj (show Paths C from a.left))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator_simplex W τ i h θ hθ)

lemma generatorTarget_simplex :
    (Functor.const (Fin (m.unop.len + 1))).obj
      (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ).right) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ ⋙ (Functor.const (Fin (n.unop.len + 1))).obj
      (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).right) :=
  congrArg (fun a => (Functor.const (Fin (m.unop.len + 1))).obj (show Paths C from a.right))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator_simplex W τ i h θ hθ)

lemma leftBlock_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock W τ i h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.leftBlock]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_precomp W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W τ i h)
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).endpoint_right_mem f) (fun _ => W.paths.id_mem _)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_heq W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceJoint_simplex W τ i θ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorSource_simplex W τ i h θ hθ) _ _
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i).endpoint_right_mem f)
    (fun _ => W.paths.id_mem _)
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).endpoint_right_mem ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ).map f))
    (fun _ => W.paths.id_mem _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftAttachment_simplex W τ i h θ hθ)

lemma rightBlock_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock W τ i h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.rightBlock]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_precomp W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment W τ i h)
    (fun _ => W.paths.id_mem _) (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).endpoint_left_mem f)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_heq W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorTarget_simplex W τ i h θ hθ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetJoint_simplex W τ i θ) _ _ (fun _ => W.paths.id_mem _)
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i).endpoint_left_mem f)
    (fun _ => W.paths.id_mem _)
    (fun f => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).endpoint_left_mem ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ).map f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightAttachment_simplex W τ i h θ hθ)

lemma generatorBlock_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ i h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_precomp W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap W τ i h)
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagram_heq W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorSource_simplex W τ i h θ hθ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorTarget_simplex W τ i h θ hθ) _ _
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap_simplex W τ i h θ hθ)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
