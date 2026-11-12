module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorCutVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplitBlocks

/-!
# 元の前後の連続部分の包含と制限射の cut

概要：制限射の cut の元の位置を前後の連続部分の包含で照合する。
方針：証明済みの元の cut の頂点の回収を使う。
規約：同じ元の語の頂点での等式である。
使われ方：切断因子の外側の方向付き列の区間比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (i : Fin a.length)

lemma prefixCutVertex_block (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)).length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock a i).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixCutVertex f i k) =
      f.cut ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock b (f.orderHom i)).vertex k) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeBlock_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixCutVertex_original f i k

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixCutVertex_block export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixCutVertex_block)


lemma residualCutVertex_block (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock a i).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex f i k) =
      f.cut ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock b (f.orderHom i)).vertex k) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterBlock_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualCutVertex_original f i k

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualCutVertex_block export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualCutVertex_block)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
