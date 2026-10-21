module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedBeforeData

/-!
# 元の貼り戻しの後の全図式の元の残りへの照合

概要：生成位置の後の全頂点・全横列・全縦成分を元の残りへ回収する。
方針：元の afterBlock の位置と連結の右側の回収式を使う。
規約：接合点・空の残りの語も含めた元の全行・全射を保持する。
使われ方：元の残りの hammock の点の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : FactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (graph W.paths b g.val.right Y).obj n)

lemma after_vertex (d : Fin (n.unop.len + 1))
    (j : Fin ((Word.ColumnSplit.after
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b)).length + 1)) :
    ((Attachments.afterDiagram W (simplex W g σ τ) (columnIndex a b)).obj d).vertex j =
      (τ.obj d).vertex (Fin.cast (congrArg (fun w : Word => w.length + 1) (after_word a b)) j) := by
  let S := (AllMarked.graphMap W X g.val.left a).app n σ
  let A := arrowSimplex W.paths g.val.hom.toPath n
  let j' := Fin.cast (congrArg (fun w : Word => w.length + 1) (after_word a b)) j
  have he := Zigzag.MovingDiagram.ColumnSplit.after_vertex (columnIndex a b)
    (Zigzag.MovingDiagram.ofFunctor (simplex W g σ τ)) d j
  have hj : Word.ColumnSplit.afterVertex
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b) j =
      Word.rightVertex (Word.append a (Word.single .forward)) b j' := Fin.ext rfl
  exact he.trans ((congrArg ((simplex W g σ τ).obj d).vertex hj).trans
    (ZigzagAppend.vertex_right (ZigzagAppend.obj (S.obj d) (A.obj d)) (τ.obj d) j'))

lemma after_arrow (d : Fin (n.unop.len + 1))
    (j : Fin (Word.ColumnSplit.after
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b)).length) :
    HEq (((Attachments.afterDiagram W (simplex W g σ τ) (columnIndex a b)).obj d).arrow j)
      ((τ.obj d).arrow (Fin.cast (congrArg Word.length (after_word a b)) j)) := by
  let S := (AllMarked.graphMap W X g.val.left a).app n σ
  let A := arrowSimplex W.paths g.val.hom.toPath n
  let j' := Fin.cast (congrArg Word.length (after_word a b)) j
  have he := Zigzag.MovingDiagram.ColumnSplit.after_arrow (columnIndex a b)
    (Zigzag.MovingDiagram.ofFunctor (simplex W g σ τ)) d j
  have hj : ((Word.ColumnSplit.afterBlock
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b)).column j) =
      j'.natAdd (Word.append a (Word.single .forward)).length := Fin.ext rfl
  exact he.trans ((ZigzagAppend.arrow_index_heq ((simplex W g σ τ).obj d) hj).trans
    (ZigzagAppend.arrow_right_heq (ZigzagAppend.obj (S.obj d) (A.obj d)) (τ.obj d) j'))

lemma after_map_app {d e : Fin (n.unop.len + 1)} (f : d ⟶ e)
    (j : Fin ((Word.ColumnSplit.after
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b)).length + 1)) :
    HEq (((Attachments.afterDiagram W (simplex W g σ τ) (columnIndex a b)).map f).app j)
      ((τ.map f).app (Fin.cast (congrArg (fun w : Word => w.length + 1) (after_word a b)) j)) := by
  let S := (AllMarked.graphMap W X g.val.left a).app n σ
  let A := arrowSimplex W.paths g.val.hom.toPath n
  let j' := Fin.cast (congrArg (fun w : Word => w.length + 1) (after_word a b)) j
  have he := Zigzag.MovingDiagram.ColumnSplit.after_map_app (columnIndex a b)
    (Zigzag.MovingDiagram.ofFunctor (simplex W g σ τ)) f j
  have hj : Word.ColumnSplit.afterVertex
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b) j =
      Word.rightVertex (Word.append a (Word.single .forward)) b j' := Fin.ext rfl
  exact he.trans ((Zigzag.app_heq ((simplex W g σ τ).map f) hj).trans
    (ZigzagAppend.app_right_heq (ZigzagAppend.map (S.map f) (A.map f)) (τ.map f) j'))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
