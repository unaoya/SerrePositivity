module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceCompleteness

/-!
模型。文献の定義との比較は後で
# 出現境界までに消費する部分語の個数

概要：Berger–Fresse §1.5.7 の各出現以前の指定値の個数が、その出現番号に等しいことを示す。
方針：最初以前と連続出現間の不出現を使って前半の count を更新する。
規約：現在の出現自身は前半に含めない。
使われ方：substitute_append の後半へ渡す部分語列の drop の添字を決める。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：位置区間に指定値がなければ実際の部分リストにもない（BF §1.5.7）。
方針：drop・take の所属を元の有限位置へ戻す。
規約：半開区間 [a,b) を使い、空区間も許す。
使われ方：出現以前と出現間の count を零へ同定する。 -/
lemma not_mem_ofFn_slice {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) (a b : ℕ)
    (h : ∀ p : Fin l, a ≤ p.val → p.val < b → v p ≠ k) :
    k ∉ ((List.ofFn v).drop a).take (b - a) := by
  intro hm
  obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hm
  have hlen := (Nat.lt_min.mp hj).2
  have hrange := (Nat.lt_min.mp hj).1
  have hb : a + j < l := by
    simp only [List.length_drop, List.length_ofFn] at hlen
    omega
  exact h ⟨a + j, hb⟩ (by change a ≤ a + j; omega) (by change a + j < b; omega)
    (by simpa only [List.getElem_drop, List.getElem_ofFn] using he)

/-- 概要：第 j 出現以前の指定値の個数は j（BF §1.5.7）。
方針：隣接出現の間の count が零であることを使って出現番号で帰納する。
規約：現在の出現自身は含めない。
使われ方：外側語を出現境界で切った代入の消費済み部分語数。 -/
lemma occurrenceAt_count_take {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) :
    ((List.ofFn v).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val).count k = j.val := by
  have H : ∀ i (hi : i < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k),
      ((List.ofFn v).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k ⟨i, hi⟩).val).count k = i := by
    intro i
    induction i with
    | zero =>
      intro hi
      apply List.count_eq_zero.mpr
      have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_ofFn_slice v k 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k ⟨0, hi⟩).val
        (fun p _ hp => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_none_before_first v k hi p hp)
      simpa only [List.drop_zero, Nat.sub_zero] using hn
    | succ i ih =>
      intro hi
      let a : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k) := ⟨i, by omega⟩
      let b : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k) := ⟨i + 1, hi⟩
      have hab := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono v k (show a < b by change i < i + 1; omega)
      have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_ofFn_slice v k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k a).val + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k b).val (fun p hp hq =>
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_none_between v k a b rfl p (by change _ < p.val; omega) hq)
      have hsplit : (List.ofFn v).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k b).val =
          (List.ofFn v).take ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k a).val + 1) ++
            ((List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k a).val + 1)).take
              ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k b).val - ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k a).val + 1)) := by
        rw [← List.take_add]
        congr 1
        change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k a).val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k b).val at hab
        omega
      have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k a).val < (List.ofFn v).length := by
        simpa only [List.length_ofFn] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k a).isLt
      rw [hsplit, List.count_append, List.count_eq_zero.mpr hn, Nat.add_zero,
        List.take_succ_eq_append_getElem hp, List.count_append]
      have hv : (List.ofFn v)[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k a).val] = k := by
        simpa only [List.getElem_ofFn] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value v k a
      rw [hv]
      simpa only [List.count_cons_self, List.count_nil, Nat.zero_add] using
        congrArg (fun x => x + 1) (ih a.isLt)
  exact H j.val j.isLt

/-- 概要：第 j 出現自身までの指定値の個数は j+1（BF §1.5.7）。
方針：その出現直前までの個数に実際の指定値一つを加える。
規約：位置の右端を含むため take の長さを一つ増やす。
使われ方：その出現を代入し終えた後の消費済み部分語数。 -/
lemma occurrenceAt_count_take_succ {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) :
    ((List.ofFn v).take ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val + 1)).count k = j.val + 1 := by
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).val < (List.ofFn v).length := by
    simpa only [List.length_ofFn] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j).isLt
  rw [List.take_succ_eq_append_getElem hp, List.count_append, List.getElem_ofFn,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value v k j, List.count_cons_self, List.count_nil, Nat.zero_add,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_count_take v k j]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
