module

public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachmentSimplex
public import SerrePositivity.EInfinity.Hammock.ForwardZigzagDiagramTransport
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendTransport

/-!
# 内部接続の三つの一列の全図式と全単体作用素

概要：接頭列・生成矢・残りの全一列の図式を元の再添字へ照合する。
方針：生成矢の端点の表示と接続自然変換の異種等式を移す。
規約：全行・全縦射・元の接合点関手を保持する。
使われ方：prefix・残り・refined 全図式の単体的整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization Zigzag.MovingDiagram

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : column W (((graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma generatorSource_simplex :
    (Functor.const (Fin (m.unop.len + 1))).obj
      (show Paths C from (rowGenerator W ((graph W.paths w X Y).map θ τ) i hθ).left) =
    rowIndex θ ⋙ (Functor.const (Fin (n.unop.len + 1))).obj
      (show Paths C from (rowGenerator W τ i h).left) :=
  congrArg (fun a => (Functor.const (Fin (m.unop.len + 1))).obj (show Paths C from a.left))
    (rowGenerator_simplex W τ i h θ hθ)

lemma generatorTarget_simplex :
    (Functor.const (Fin (m.unop.len + 1))).obj
      (show Paths C from (rowGenerator W ((graph W.paths w X Y).map θ τ) i hθ).right) =
    rowIndex θ ⋙ (Functor.const (Fin (n.unop.len + 1))).obj
      (show Paths C from (rowGenerator W τ i h).right) :=
  congrArg (fun a => (Functor.const (Fin (m.unop.len + 1))).obj (show Paths C from a.right))
    (rowGenerator_simplex W τ i h θ hθ)

lemma leftBlock_simplex :
    HEq (leftBlock W ((graph W.paths w X Y).map θ τ) i hθ)
      ((leftBlock W τ i h).precomp (rowIndex θ)) := by
  dsimp only [leftBlock]
  rw [ForwardZigzag.diagram_precomp W.paths (rowIndex θ) (leftAttachment W τ i h)
    (fun f => (beforeDiagram W τ i).endpoint_right_mem f) (fun _ => W.paths.id_mem _)]
  exact ForwardZigzag.diagram_heq W.paths (sourceJoint_simplex W τ i θ)
    (generatorSource_simplex W τ i h θ hθ) _ _
    (fun f => (beforeDiagram W ((graph W.paths w X Y).map θ τ) i).endpoint_right_mem f)
    (fun _ => W.paths.id_mem _)
    (fun f => (beforeDiagram W τ i).endpoint_right_mem ((rowIndex θ).map f))
    (fun _ => W.paths.id_mem _)
    (leftAttachment_simplex W τ i h θ hθ)

lemma rightBlock_simplex :
    HEq (rightBlock W ((graph W.paths w X Y).map θ τ) i hθ)
      ((rightBlock W τ i h).precomp (rowIndex θ)) := by
  dsimp only [rightBlock]
  rw [ForwardZigzag.diagram_precomp W.paths (rowIndex θ) (rightAttachment W τ i h)
    (fun _ => W.paths.id_mem _) (fun f => (afterDiagram W τ i).endpoint_left_mem f)]
  exact ForwardZigzag.diagram_heq W.paths (generatorTarget_simplex W τ i h θ hθ)
    (targetJoint_simplex W τ i θ) _ _ (fun _ => W.paths.id_mem _)
    (fun f => (afterDiagram W ((graph W.paths w X Y).map θ τ) i).endpoint_left_mem f)
    (fun _ => W.paths.id_mem _)
    (fun f => (afterDiagram W τ i).endpoint_left_mem ((rowIndex θ).map f))
    (rightAttachment_simplex W τ i h θ hθ)

lemma generatorBlock_simplex :
    HEq (generatorBlock W ((graph W.paths w X Y).map θ τ) i hθ)
      ((generatorBlock W τ i h).precomp (rowIndex θ)) := by
  dsimp only [generatorBlock]
  rw [ForwardZigzag.diagram_precomp W.paths (rowIndex θ) (rowGeneratorMap W τ i h)
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)]
  exact ForwardZigzag.diagram_heq W.paths (generatorSource_simplex W τ i h θ hθ)
    (generatorTarget_simplex W τ i h θ hθ) _ _
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
    (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)
    (rowGeneratorMap_simplex W τ i h θ hθ)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
