module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Slots
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TupleAppend

/-!
模型。文献の定義との比較は後で
# 一つの出力を置換した族の前後ブロック表示

概要：Berger–Fresse §2.2.6 の部分合成の出力族を前方・挿入・後方の連結で表す。
方針：実際の operadInsertionEquiv の三つの位置範囲を連結の添字と比較する。
規約：置換する族も前後の族も空を許す。
使われ方：二段切断の出力族を実際の余代入のブロック評価へ渡す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：指定出力より前の族（BF §2.2.6）。
方針：元の有限添字へ同じ値で埋め込む。
規約：指定出力自身を含めない。
使われ方：余代入の前方ブロックとその次数。 -/
def prefixFamily {α : Type*} {m : ℕ} (f : Fin (m + 1) → α) (i : Fin (m + 1))
    (j : Fin i.val) : α := f ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩

/-- 概要：指定出力より後の族（BF §2.2.6）。
方針：指定出力の次へ後方の相対位置を加える。
規約：指定出力自身を含めない。
使われ方：余代入の後方ブロック。 -/
def suffixFamily {α : Type*} {m : ℕ} (f : Fin (m + 1) → α) (i : Fin (m + 1))
    (j : Fin (m - i.val)) : α := f ⟨i.val + 1 + j.val, by
      have := j.isLt; have := i.isLt; omega⟩

/-- 概要：指定した出力を別の族で置換した全出力族（BF §2.2.6）。
方針：部分合成の入力分解で残り色に元の族、挿入色に内側の族を割り当てる。
規約：既存の operadInsertionEquiv の入力順序を使う。
使われ方：二段切断とブロック連結の共通の族。 -/
def insertionFamily {α : Type*} {m n : ℕ} (f : Fin (m + 1) → α) (g : Fin n → α)
    (i : Fin (m + 1)) (j : Fin (m + n)) : α :=
  match _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i j with
  | Sum.inl b => f b.val
  | Sum.inr b => g b

/-- 概要：置換した全出力族は前方・挿入・後方の三ブロックの連結（BF §2.2.6）。
方針：指定位置の前・挿入区間内・後の三つで有限添字の値を照合する。
規約：最後に arity の等式で元の出力 arity へ移す。
使われ方：実際の tensorCoInsertionAction の出力族の同定。 -/
lemma insertionFamily_eq_blocks {α : Type*} {m n : ℕ} (f : Fin (m + 1) → α)
    (g : Fin n → α) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily f g i =
      Fin.append (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) (Fin.append g (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily f i)) ∘
        Fin.cast (by omega : m + n = i.val + (n + (m - i.val))) := by
  funext j
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, Equiv.coe_fn_mk, Function.comp_apply,
    Fin.append, Fin.addCases, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily, Fin.cast, Fin.castLT, Fin.subNat]
  split_ifs <;> (try omega) <;> (try rfl) <;>
    (try simp_all only [Fin.natAdd_mk, eq_rec_constant])
  congr 1
  apply Fin.ext
  dsimp
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
