module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListGenerators
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Deletion

/-!
模型。文献の定義との比較は後で
# 有限語のリスト化と一文字削除

概要：Berger–Fresse §1.2.3・§1.4.4 の有限語の削除をリストの eraseIdx と比較する。
方針：削除位置の前後で有限添字とリストの要素を照合する。
規約：正規化の前の任意の語を扱う。
使われ方：削除微分をリスト出力の位置ごとの項へ展開する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：有限列の一成分の削除とリストの eraseIdx は一致（BF §1.4.4）。
方針：削除位置の前後に分けて要素を比較する。
規約：先頭・末尾の削除も含む。
使われ方：有限語の削除項を table 出力リストの削除項に直す。 -/
lemma ofFn_succAbove_eraseIdx {α : Type*} {m : ℕ} (f : Fin (m + 1) → α)
    (i : Fin (m + 1)) : List.ofFn (fun j => f (i.succAbove j)) =
      (List.ofFn f).eraseIdx i.val := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, i.isLt]
  · intro j hj hk
    simp only [List.length_ofFn] at hj
    rw [List.getElem_ofFn, List.getElem_eraseIdx]
    split
    · rename_i hji
      rw [List.getElem_ofFn]
      congr 1
      apply Fin.ext
      simp [Fin.succAbove, Fin.lt_def, hji]
    · rename_i hji
      rw [List.getElem_ofFn]
      congr 1
      apply Fin.ext
      simp [Fin.succAbove, Fin.lt_def, hji]


end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
