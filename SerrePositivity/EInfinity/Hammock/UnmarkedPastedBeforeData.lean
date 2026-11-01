module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedWordSplit
public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedSimplex
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitArrows
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendSegments

/-!
# 元の貼り戻しの前の全図式の元の prefix への照合

概要：生成位置の前の全頂点・全横列・全縦成分を元の指定 prefix へ回収する。
方針：元の beforeBlock の位置と二段の連結の左側の回収式を使う。
規約：接合点を含めた元の全行・全射を保持する。
使われ方：元の prefix の hammock の点の回収。
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

lemma before_vertex (d : Fin (n.unop.len + 1)) (j : Fin (a.length + 1)) :
    ((Attachments.beforeDiagram W (simplex W g σ τ) (columnIndex a b)).obj d).vertex j =
      (((AllMarked.graphMap W X g.val.left a).app n σ).obj d).vertex j := by
  let S := (AllMarked.graphMap W X g.val.left a).app n σ
  let A := arrowSimplex W.paths g.val.hom.toPath n
  have he := Zigzag.MovingDiagram.ColumnSplit.before_vertex (columnIndex a b)
    (Zigzag.MovingDiagram.ofFunctor (simplex W g σ τ)) d j
  have hj : Word.ColumnSplit.beforeVertex
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b) j =
      Word.leftVertex (Word.append a (Word.single .forward)) b
        (Word.leftVertex a (Word.single .forward) j) := Fin.ext rfl
  exact he.trans ((congrArg ((simplex W g σ τ).obj d).vertex hj).trans
    ((ZigzagAppend.vertex_left (ZigzagAppend.obj (S.obj d) (A.obj d)) (τ.obj d) _).trans
      (ZigzagAppend.vertex_left (S.obj d) (A.obj d) j)))

lemma before_arrow (d : Fin (n.unop.len + 1)) (j : Fin a.length) :
    HEq (((Attachments.beforeDiagram W (simplex W g σ τ) (columnIndex a b)).obj d).arrow j)
      ((((AllMarked.graphMap W X g.val.left a).app n σ).obj d).arrow j) := by
  let S := (AllMarked.graphMap W X g.val.left a).app n σ
  let A := arrowSimplex W.paths g.val.hom.toPath n
  have he := Zigzag.MovingDiagram.ColumnSplit.before_arrow (columnIndex a b)
    (Zigzag.MovingDiagram.ofFunctor (simplex W g σ τ)) d j
  have hj : ((Word.ColumnSplit.beforeBlock
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b)).column j) =
      (j.castAdd 1).castAdd b.length := Fin.ext (by
        change 0 + j.val = j.val
        omega)
  exact he.trans ((ZigzagAppend.arrow_index_heq ((simplex W g σ τ).obj d) hj).trans
    ((ZigzagAppend.arrow_left_heq (ZigzagAppend.obj (S.obj d) (A.obj d)) (τ.obj d) _).trans
      (ZigzagAppend.arrow_left_heq (S.obj d) (A.obj d) j)))

lemma before_map_app {d e : Fin (n.unop.len + 1)} (f : d ⟶ e) (j : Fin (a.length + 1)) :
    HEq (((Attachments.beforeDiagram W (simplex W g σ τ) (columnIndex a b)).map f).app j)
      ((((AllMarked.graphMap W X g.val.left a).app n σ).map f).app j) := by
  let S := (AllMarked.graphMap W X g.val.left a).app n σ
  let A := arrowSimplex W.paths g.val.hom.toPath n
  have he := Zigzag.MovingDiagram.ColumnSplit.before_map_app (columnIndex a b)
    (Zigzag.MovingDiagram.ofFunctor (simplex W g σ τ)) f j
  have hj : Word.ColumnSplit.beforeVertex
      (Word.append (Word.append a (Word.single .forward)) b) (columnIndex a b) j =
      Word.leftVertex (Word.append a (Word.single .forward)) b
        (Word.leftVertex a (Word.single .forward) j) := Fin.ext rfl
  exact he.trans ((Zigzag.app_heq ((simplex W g σ τ).map f) hj).trans
    ((ZigzagAppend.app_left_heq (ZigzagAppend.map (S.map f) (A.map f)) (τ.map f) _).trans
      (ZigzagAppend.app_left_heq (S.map f) (A.map f) j)))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
