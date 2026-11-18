module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DonorStep

/-!
模型。文献の定義との比較は後で
# 除外を解いた後の行内の値の再出現

概要：Berger–Fresse §1.4.4 の行末削除の逆対応で、後の行を一文字延ばす局所抽出を与える。
方針：早く除外されていた値を行内部に挿入し、行通過後の除外所属を一致させる。
規約：値が新たに選択される行の元の末尾より前に入る場合を扱う。
使われ方：最初に影響を受ける後続行で、行末側から最終出現側の削除へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：除外を解いた値を行内に挿入すると元の後続抽出に合流する（BF §1.4.4）。
方針：donor の二状態の同値を逆向きに使い、長い選択を再構成する。
規約：後の行を一文字延ばし、挿入値はその新しい末尾より前に置く。
使われ方：行末削除の逆対応の、後で長さを増やす行を構成する。 -/
lemma reduceRows_released_donor_step (removed row pre post : List α) (a : α) (s : ℕ)
    (hs : 0 < s) (hb : s ≤ post.length)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = pre ++ a :: post) (hpre : a ∉ pre) (hpost : a ∉ post)
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest
      ((removed ++ [a]) ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (pre.length + s - 1)) =
        some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, pre.length + (s + 1)) :: rest) removed =
      some ((pre ++ a :: post.take s) ++ tail) := by
  have hstate := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest
    (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take (pre.length + (s + 1) - 1))
    ((removed ++ [a]) ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ [a]) row).take (pre.length + s - 1))
    (fun x => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.donor_exclusion_equiv removed row pre post a s hs he hpre hpost x).symm)
  have htail := hstate.trans ht
  have hbound : pre.length + (s + 1) ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by
    rw [he, List.length_append, List.length_cons]
    omega
  have hsuccess := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row (pre.length + (s + 1)) rest removed tail
    (by omega) hbound htail
  rw [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.donor_selected_split removed row pre post a s he hpre hpost).2] at hsuccess
  exact hsuccess

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
