module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCutFactorCutVertices
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordColumnSplitBlocks

/-!
# 元の前後の連続部分の包含と制限射の cut

概要：制限射の cut の元の位置を前後の連続部分の包含で照合する。
方針：証明済みの元の cut の頂点の回収を使う。
規約：同じ元の語の頂点での等式である。
使われ方：切断因子の外側の方向付き列の区間比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.CutFactor
open CategoryTheory

variable {a b : Word} (f : a ⟶ b) (i : Fin a.length)

lemma prefixCutVertex_block (k : Fin ((ColumnSplit.before b (f.orderHom i)).length + 1)) :
    (ColumnSplit.beforeBlock a i).vertex (prefixCutVertex f i k) =
      f.cut ((ColumnSplit.beforeBlock b (f.orderHom i)).vertex k) := by
  rw [ColumnSplit.beforeBlock_vertex, ColumnSplit.beforeBlock_vertex]
  exact prefixCutVertex_original f i k

lemma residualCutVertex_block (k : Fin ((ColumnSplit.after b (f.orderHom i)).length + 1)) :
    (ColumnSplit.afterBlock a i).vertex (residualCutVertex f i k) =
      f.cut ((ColumnSplit.afterBlock b (f.orderHom i)).vertex k) := by
  rw [ColumnSplit.afterBlock_vertex, ColumnSplit.afterBlock_vertex]
  exact residualCutVertex_original f i k

end SerrePositivity.EInfinity.Hammock.Word.CutFactor
