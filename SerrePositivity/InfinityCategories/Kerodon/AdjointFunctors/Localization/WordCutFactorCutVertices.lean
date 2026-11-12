module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorResidualCuts

/-!
# 制限した cut の元の前後の頂点での表示

概要：制限射の cut を prefix の前・残りの後の埋め込みとして回収する。
方針：元の cut の数値公式と切断列の左右の境界を使う。
規約：元の cut 自身を回収し、等しい値だけで止めない。
使われ方：切断因子の全頂点・全縦射の語の作用への比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (i : Fin a.length)

def prefixCutVertex (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)).length + 1)) :
    Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before a i).length + 1) :=
  ⟨(f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixVertex b (f.orderHom i) k)).val,
    Nat.lt_succ_of_le (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_le_column f i _ (Nat.le_of_lt_succ k.isLt))⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixCutVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixCutVertex)


def residualCutVertex (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).length + 1)) :
    Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after a i).length + 1) :=
  ⟨(f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k)).val - i.val - 1, by
    have hc := (f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k)).isLt
    have hi := i.isLt
    change (f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k)).val - i.val - 1 <
      a.length - i.val - 1 + 1
    omega⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualCutVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualCutVertex)


lemma prefixCutVertex_original
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)).length + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixVertex a i (prefixCutVertex f i k) = f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixVertex b (f.orderHom i) k) :=
  Fin.ext rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefixCutVertex_original export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixCutVertex_original)


lemma residualCutVertex_original
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).length + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex a i (residualCutVertex f i k) = f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k) := by
  have hc : i.val < (f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k)).val :=
    (f.lt_cut_iff _ i).2 (by change (f.orderHom i).val < (f.orderHom i).val + 1 + k.val; omega)
  apply Fin.ext
  change i.val + 1 + ((f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k)).val - i.val - 1) = _
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residualCutVertex_original export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualCutVertex_original)


variable (hi : a.direction i = .forward)

lemma prefix_cut_eq (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)).length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f i hi).cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before b (f.orderHom i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before a i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (prefixCutVertex f i k) :=
  Fin.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_cut f i hi k)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.prefix_cut_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefix_cut_eq)


lemma residual_cut_eq (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)).length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom i)) k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after a i) (residualCutVertex f i k) := by
  apply Fin.ext
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_cut f i hi k
  have hc : i.val < (f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k)).val :=
    (f.lt_cut_iff _ i).2 (by change (f.orderHom i).val < (f.orderHom i).val + 1 + k.val; omega)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f i hi).cut _).val =
    1 + ((f.cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualVertex b (f.orderHom i) k)).val - i.val - 1)
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.CutFactor.residual_cut_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residual_cut_eq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
