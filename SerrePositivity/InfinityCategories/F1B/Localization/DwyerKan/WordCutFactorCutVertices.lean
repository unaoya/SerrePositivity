module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCutFactorResidualCuts

/-!
# 制限した cut の元の前後の頂点での表示

概要：制限射の cut を prefix の前・残りの後の埋め込みとして回収する。
方針：元の cut の数値公式と切断列の左右の境界を使う。
規約：元の cut 自身を回収し、等しい値だけで止めない。
使われ方：切断因子の全頂点・全縦射の語の作用への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.CutFactor
open CategoryTheory

variable {a b : Word} (f : a ⟶ b) (i : Fin a.length)

def prefixCutVertex (k : Fin ((ColumnSplit.before b (f.orderHom i)).length + 1)) :
    Fin ((ColumnSplit.before a i).length + 1) :=
  ⟨(f.cut (prefixVertex b (f.orderHom i) k)).val,
    Nat.lt_succ_of_le (cut_le_column f i _ (Nat.le_of_lt_succ k.isLt))⟩

def residualCutVertex (k : Fin ((ColumnSplit.after b (f.orderHom i)).length + 1)) :
    Fin ((ColumnSplit.after a i).length + 1) :=
  ⟨(f.cut (residualVertex b (f.orderHom i) k)).val - i.val - 1, by
    have hc := (f.cut (residualVertex b (f.orderHom i) k)).isLt
    have hi := i.isLt
    change (f.cut (residualVertex b (f.orderHom i) k)).val - i.val - 1 <
      a.length - i.val - 1 + 1
    omega⟩

lemma prefixCutVertex_original
    (k : Fin ((ColumnSplit.before b (f.orderHom i)).length + 1)) :
    prefixVertex a i (prefixCutVertex f i k) = f.cut (prefixVertex b (f.orderHom i) k) :=
  Fin.ext rfl

lemma residualCutVertex_original
    (k : Fin ((ColumnSplit.after b (f.orderHom i)).length + 1)) :
    residualVertex a i (residualCutVertex f i k) = f.cut (residualVertex b (f.orderHom i) k) := by
  have hc : i.val < (f.cut (residualVertex b (f.orderHom i) k)).val :=
    (f.lt_cut_iff _ i).2 (by change (f.orderHom i).val < (f.orderHom i).val + 1 + k.val; omega)
  apply Fin.ext
  change i.val + 1 + ((f.cut (residualVertex b (f.orderHom i) k)).val - i.val - 1) = _
  omega

variable (hi : a.direction i = .forward)

lemma prefix_cut_eq (k : Fin ((ColumnSplit.before b (f.orderHom i)).length + 1)) :
    (prefixMap f i hi).cut (leftVertex (ColumnSplit.before b (f.orderHom i)) (single .forward) k) =
      leftVertex (ColumnSplit.before a i) (single .forward) (prefixCutVertex f i k) :=
  Fin.ext (prefix_cut f i hi k)

lemma residual_cut_eq (k : Fin ((ColumnSplit.after b (f.orderHom i)).length + 1)) :
    (residualMap f i hi).cut
      (rightVertex (single .forward) (ColumnSplit.after b (f.orderHom i)) k) =
      rightVertex (single .forward) (ColumnSplit.after a i) (residualCutVertex f i k) := by
  apply Fin.ext
  have he := residual_cut f i hi k
  have hc : i.val < (f.cut (residualVertex b (f.orderHom i) k)).val :=
    (f.lt_cut_iff _ i).2 (by change (f.orderHom i).val < (f.orderHom i).val + 1 + k.val; omega)
  change ((residualMap f i hi).cut _).val =
    1 + ((f.cut (residualVertex b (f.orderHom i) k)).val - i.val - 1)
  omega

end SerrePositivity.EInfinity.Hammock.Word.CutFactor
