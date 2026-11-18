module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.InsertedOccurrences

/-!
模型。文献の定義との比較は後で
# 等しい語の最終出現の一意性

概要：Berger–Fresse §1.4.4 の往復の削除位置を最終出現から同定する。
方針：二つの位置が異なれば前の位置に後の同値の出現がある。
規約：語の長さと位置の証明項が異なってもよい。
使われ方：復元した成功出力で元と逆構成の削除位置を一致させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：等しい二語の同じ値の最終出現は同じ位置（BF §1.4.4）。
方針：位置の大小を比較し、真の不等号の二分岐を最終出現性で排除する。
規約：二つの有限添字はそれぞれのリスト長を持つ。
使われ方：成功出力が一致した後の削除点の復元に用いる。 -/
lemma final_occurrence_unique {n : ℕ} (xs ys : List (Fin n)) (he : xs = ys)
    (i : Fin xs.length) (j : Fin ys.length)
    (hi : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun k : Fin xs.length => xs[k.val]) i)
    (hj : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun k : Fin ys.length => ys[k.val]) j)
    (hv : xs[i.val] = ys[j.val]) : i.val = j.val := by
  have hlen := congrArg List.length he
  rcases lt_trichotomy i.val j.val with hij | heq | hji
  · have hb : j.val < xs.length := by have := j.isLt; omega
    apply False.elim
    apply hi
    refine ⟨⟨j.val, hb⟩, hij, ?_⟩
    exact (List.getElem_of_eq he hb).trans hv.symm
  · exact heq
  · have hb : i.val < ys.length := by have := i.isLt; omega
    apply False.elim
    apply hj
    refine ⟨⟨i.val, hb⟩, hji, ?_⟩
    exact (List.getElem_of_eq he i.isLt).symm.trans hv

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
