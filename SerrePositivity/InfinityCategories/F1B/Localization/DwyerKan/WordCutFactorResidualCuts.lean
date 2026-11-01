module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCutFactorPrefixCuts

/-!
# 元の残りの語の制限射の全切断位置

概要：残りの後の全頂点の cut を、切断列の位置を足して元の cut へ戻す。
方針：元の全列の初期区間の特徴付けと切断列の左右での場合分けを使う。
規約：元の頂点番号と空 fiber を保持する。
使われ方：残りの全図式の語の作用への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.CutFactor
open CategoryTheory

variable {a b : Word} (f : a ⟶ b) (i : Fin a.length) (hi : a.direction i = .forward)

lemma residual_cut (k : Fin ((ColumnSplit.after b (f.orderHom i)).length + 1)) :
    i.val + ((residualMap f i hi).cut
      (rightVertex (single .forward) (ColumnSplit.after b (f.orderHom i)) k)).val =
      (f.cut (residualVertex b (f.orderHom i) k)).val := by
  let s := rightVertex (single .forward) (ColumnSplit.after b (f.orderHom i)) k
  let t := residualVertex b (f.orderHom i) k
  let p : Fin (a.length + 1) :=
    ⟨i.val + ((residualMap f i hi).cut s).val, by
      have hp := ((residualMap f i hi).cut s).isLt
      have hiBound := i.isLt
      change ((residualMap f i hi).cut s).val < 1 + (a.length - i.val - 1) + 1 at hp
      omega⟩
  have he : p = f.cut t := by
    apply Hom.vertex_ext
    intro l
    rw [f.lt_cut_iff]
    by_cases hl : l.val < i.val
    · have hm := f.orderHom.monotone (show l ≤ i by omega)
      change (f.orderHom l).val ≤ (f.orderHom i).val at hm
      constructor
      · intro _
        change (f.orderHom l).val < (f.orderHom i).val + 1 + k.val
        omega
      · intro _
        change l.val < i.val + ((residualMap f i hi).cut s).val
        omega
    · let r : Fin (residualWord a i).length := ⟨l.val - i.val, by
        have hl' := l.isLt
        have hi' := i.isLt
        change l.val - i.val < 1 + (a.length - i.val - 1)
        omega⟩
      have hr : residualColumn a i r = l := by
        apply Fin.ext
        change i.val + (l.val - i.val) = l.val
        omega
      have hm := f.orderHom.monotone (le_residualColumn a i r)
      rw [hr] at hm
      change (f.orderHom i).val ≤ (f.orderHom l).val at hm
      have hc := (residualMap f i hi).lt_cut_iff s r
      change l.val - i.val < ((residualMap f i hi).cut s).val ↔
        (f.orderHom (residualColumn a i r)).val - (f.orderHom i).val < 1 + k.val at hc
      rw [hr] at hc
      change l.val < i.val + ((residualMap f i hi).cut s).val ↔
        (f.orderHom l).val < (f.orderHom i).val + 1 + k.val
      omega
  exact congrArg Fin.val he

end SerrePositivity.EInfinity.Hammock.Word.CutFactor
