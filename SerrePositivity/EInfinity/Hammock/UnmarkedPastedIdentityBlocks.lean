module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedSelectedBlocks
public import SerrePositivity.EInfinity.Hammock.ForwardZigzagDiagramTransport

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
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : FactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, column W ((simplex W g σ τ).obj 0) j ≠ [])

lemma leftBlock_identity :
    HEq (Attachments.leftBlock W (simplex W g σ τ)
      (AttachedPrefix.index W (simplex W g σ τ) h) (AttachedPrefix.nonempty W _ h))
      (ForwardZigzag.diagram W.paths
        (𝟙 ((Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.left)))
        (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)) := by
  have hB := congrArg (fun t : Quiver.Total C =>
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from t.left))
      (simplex_generator W g σ τ h)
  exact ForwardZigzag.diagram_heq W.paths (selected_sourceJoint_eq W g σ τ h) hB
    _ _ (fun f => (Attachments.beforeDiagram W (simplex W g σ τ)
      (AttachedPrefix.index W (simplex W g σ τ) h)).endpoint_right_mem f)
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
    (GeneratorWord.zeroNatTrans_heq_id _
      (leftAttachment_length_zero W g σ τ h) hB)

lemma rightBlock_identity :
    HEq (Attachments.rightBlock W (simplex W g σ τ)
      (AttachedPrefix.index W (simplex W g σ τ) h) (AttachedPrefix.nonempty W _ h))
      (ForwardZigzag.diagram W.paths
        (𝟙 ((Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.right)))
        (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)) := by
  have hA := congrArg (fun t : Quiver.Total C =>
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from t.right))
      (simplex_generator W g σ τ h)
  exact ForwardZigzag.diagram_heq W.paths hA (selected_targetJoint_eq W g σ τ h)
    _ _ (fun _ => W.paths.id_mem _)
    (fun f => (Attachments.afterDiagram W (simplex W g σ τ)
      (AttachedPrefix.index W (simplex W g σ τ) h)).endpoint_left_mem f)
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
    (GeneratorWord.zeroNatTrans_heq_id _
      (rightAttachment_length_zero W g σ τ h) (selected_targetJoint_eq W g σ τ h))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
