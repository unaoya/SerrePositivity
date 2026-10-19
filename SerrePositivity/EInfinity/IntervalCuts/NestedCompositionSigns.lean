module

public import SerrePositivity.EInfinity.IntervalCuts.CutSegmentDegrees
public import SerrePositivity.EInfinity.IntervalCuts.NestedCutValidity

/-!
# 二段切断で選ばれる部分合成符号の簡約

概要：Berger–Fresse §1.2.5・§2.2.6 の二段切断の合成符号を各入力分岐で計算する。
方針：切断点色分岐では後続外側次数が零、二出現分岐では最初の内側成分だけが全次数を持つ。
規約：元の compositionExponent・compositionSign を変更せず評価する。
使われ方：合成切断符号と二段作用の Koszul 符号の照合。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut

open Surjection

variable {m n d e : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord n e} {k : Fin (m + 1)}

/-- 概要：外側切断点色への代入の合成指数は零（BF §2.2.6）。
方針：指定色は一出現で、その行番号が全外側次数なので後続次数が零。
規約：内側語次数は任意。
使われ方：切断点色分岐の合成符号を一へ簡約する。 -/
lemma compositionExponent_pivot (a : NestedEdgeCut u v k) (hp : u.val a.val.1 = k) :
    compositionExponent u v k a.partition = 0 := by
  have hc : occurrenceCount u.val k = 1 := by
    rw [← hp]
    exact occurrenceCount_pivot_eq_one u a.val.1 a.property.1
  unfold compositionExponent
  apply Finset.sum_eq_zero
  intro j _
  rw [occurrenceAt_of_count_one u.val k hc a.val.1 hp j,
    caesuraRank_pivot_eq_degree u a.val.1 a.property.1, Nat.sub_self, mul_zero]

/-- 概要：外側切断点色への代入の合成符号は正（BF §2.2.6）。
方針：元の合成符号へ零の合成指数を代入する。
規約：整数符号で述べる。
使われ方：切断符号だけを二段作用の符号と比較する。 -/
lemma compositionSign_pivot (a : NestedEdgeCut u v k) (hp : u.val a.val.1 = k) :
    compositionSign u v k a.partition = 1 := by
  rw [compositionSign, compositionExponent_pivot a hp, pow_zero]

/-- 概要：二出現分岐の第一部分語次数は内側全次数、第二は零（BF §2.2.6）。
方針：構成した分割を標準二部分割へ移して両行次数を評価する。
規約：元の出現添字を保持する。
使われ方：合成指数の有限和を最初の指定出現一つへ集約する。 -/
lemma partition_segmentDegree_nonpivot (a : NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k)
    (j : Fin (occurrenceCount u.val k)) :
    segmentDegree v.val a.partition j = if j.val = 0 then e else 0 := by
  have hc := a.occurrenceCount_eq_two_of_some_nonpivot q ha (Ne.symm hp)
  let j' : Fin 2 := ⟨j.val, by have := j.isLt; omega⟩
  rw [← segmentDegree_cast_count hc a.partition v.val j j' rfl,
    partition_of_some_nonpivot a q ha (Ne.symm hp)]
  have H (i : Fin 2) : segmentDegree v.val (OverlapPartition.two q) i =
      if i.val = 0 then e else 0 := by
    have hq := a.property.2
    rw [ha] at hq
    fin_cases i
    · change segmentDegree v.val (OverlapPartition.two q) 0 = e
      exact segmentDegree_two_zero v q hq.2
    · change segmentDegree v.val (OverlapPartition.two q) 1 = 0
      exact segmentDegree_two_one v q hq.2
  exact H j'

/-- 概要：二出現分岐の合成指数は内側次数と最初の出現以後の外側次数の積（BF §2.2.6）。
方針：第二部分語の零次数で和の全ての他項を消す。
規約：最初の指定出現は既存の occurrenceAt の零番号。
使われ方：右辺の係数交換と出力因子交換の符号へ比較する。 -/
lemma compositionExponent_nonpivot (a : NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    compositionExponent u v k a.partition = e *
      (d - caesuraRank u.val (occurrenceAt u.val k ⟨0, occurrenceCount_pos u k⟩)) := by
  let i : Fin (occurrenceCount u.val k) := ⟨0, occurrenceCount_pos u k⟩
  unfold compositionExponent
  calc
    _ = segmentDegree v.val a.partition i *
        (d - caesuraRank u.val (occurrenceAt u.val k i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have hj : j.val ≠ 0 := fun h => hji (Fin.ext h)
        rw [partition_segmentDegree_nonpivot a q ha hp j, ite_eq_right hj, zero_mul]
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    _ = _ := by
      rw [partition_segmentDegree_nonpivot a q ha hp i, ite_eq_left rfl]

/-- 概要：二出現分岐の合成符号は最初の指定出現の後続次数で決まる（BF §2.2.6）。
方針：簡約した合成指数を元の整数符号に代入する。
規約：外側・内側次数は任意。
使われ方：合成切断の逆転数による符号との一般比較。 -/
lemma compositionSign_nonpivot (a : NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    compositionSign u v k a.partition = (-1 : ℤ) ^ (e *
      (d - caesuraRank u.val (occurrenceAt u.val k ⟨0, occurrenceCount_pos u k⟩))) := by
  rw [compositionSign, compositionExponent_nonpivot a q ha hp]

/-- 概要：内側頂点入力分岐の合成符号は正（BF §2.2.6）。
方針：頂点入力の内側次数零を既存の合成符号公式へ渡す。
規約：内側空語も含む。
使われ方：頂点分岐では外側切断符号だけが残ること。 -/
lemma compositionSign_vertex (a : NestedEdgeCut u v k) (ha : a.val.2 = none) :
    compositionSign u v k a.partition = 1 := by
  have H := a.property.2
  rw [ha] at H
  have he := H.2
  subst e
  exact compositionSign_inner_degree_zero u v k a.partition

end SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut
