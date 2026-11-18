module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapSegments
public import Mathlib.Data.Finset.Max

/-!
模型。文献の定義との比較は後で
# 端点を重ねた部分語は元の語を覆う

概要：Berger–Fresse §1.2.4 の全部分語の和集合が内側の全ての位置を含むことを示す。
方針：開始位置が指定位置以下である最後の部分語を取り、次の開始との共有を使う。
規約：語に位置があれば非空、分割数は正とする。
使われ方：部分合成の合成語の全射性を保証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

variable {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)

/-- 概要：次の部分語は前の部分語の末尾から始まる（BF §1.2.4）。
方針：開始位置の部分和を一成分だけ増やす。
規約：添字は自然数値が一つ増える二つの有限添字。
使われ方：分割区間の間に空隙がないことを示す。 -/
lemma start_next (i j : Fin t) (hij : j.val = i.val + 1) :
    r.start j = r.start i + ((r.val i).val - 1) := by
  have hi : i.val < (List.ofFn (fun k => (r.val k).val - 1)).length := by
    simpa only [List.length_ofFn] using i.isLt
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.start
  rw [hij, List.take_succ_eq_append_getElem hi, List.sum_append]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.getElem_ofFn]

/-- 概要：最後の部分語の終了境界は元の語の終了境界（BF §1.2.4）。
方針：最後の一成分を含む部分和は全ステップの総和。
規約：元の語は非空。
使われ方：最大の開始位置を持つ部分語も最後の位置まで覆う。 -/
lemma last_end (hl : 0 < l) (i : Fin t) (hi : i.val + 1 = t) :
    r.start i + (r.val i).val = l := by
  have hs := r.sum_steps hl
  have hib : i.val < (List.ofFn (fun j => (r.val j).val - 1)).length := by
    simpa only [List.length_ofFn] using i.isLt
  have he := List.take_succ_eq_append_getElem hib
  rw [hi] at he
  have htake : (List.ofFn (fun j => (r.val j).val - 1)).take t =
      List.ofFn (fun j => (r.val j).val - 1) :=
    List.take_of_length_le (by rw [List.length_ofFn])
  rw [htake] at he
  have hh := congrArg List.sum he
  simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.getElem_ofFn, List.sum_ofFn] at hh
  change (∑ j, ((r.val j).val - 1)) =
    ((List.ofFn (fun j => (r.val j).val - 1)).take i.val).sum + ((r.val i).val - 1) at hh
  have hp := r.positive hl i
  change r.start i + (r.val i).val = l
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.start
  omega

/-- 概要：元の各位置は少なくとも一つの部分語に属する（BF §1.2.4）。
方針：その位置以下の開始を持つ最大の部分語を取り、次への進行と最後の境界を使う。
規約：分割数は正。共有端点ではどちらの部分語を選んでもよい。
使われ方：内側の値を合成語のいずれかの挿入部分で見つける。 -/
lemma position_covered (ht : 0 < t) (p : Fin l) :
    ∃ i : Fin t, r.start i ≤ p.val ∧ p.val < r.start i + (r.val i).val := by
  let s := Finset.univ.filter (fun i : Fin t => r.start i ≤ p.val)
  have hs : s.Nonempty := ⟨⟨0, ht⟩, by simp [s]⟩
  let i := s.max' hs
  have himem : i ∈ s := Finset.max'_mem s hs
  have hstart : r.start i ≤ p.val := (Finset.mem_filter.mp himem).2
  refine ⟨i, hstart, ?_⟩
  by_contra hn
  have hl : 0 < l := by have := p.isLt; omega
  have hipos := r.positive hl i
  by_cases hi : i.val + 1 = t
  · have hend := r.last_end hl i hi
    have := p.isLt
    omega
  · let j : Fin t := ⟨i.val + 1, by have := i.isLt; omega⟩
    have hnext := r.start_next i j rfl
    have hj : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hle := Finset.le_max' s j hj
    change j.val ≤ i.val at hle
    dsimp only [j] at hle
    omega

/-- 概要：元の語の全ての値は分割部分語の平坦化にも現れる（BF §1.2.4）。
方針：各位置を覆う部分語を取り、drop と take の中の対応する添字を使う。
規約：分割数は正、元の語の値の重複は許す。
使われ方：部分合成により内側の全ての入力値が失われないことを示す。 -/
lemma value_mem_segments {α : Type*} (v : Fin l → α) (ht : 0 < t) (p : Fin l) :
    v p ∈ (r.segments v).flatten := by
  obtain ⟨i, hlo, hhi⟩ := r.position_covered ht p
  apply List.mem_flatten.mpr
  refine ⟨r.segment v i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  have hb : p.val - r.start i < ((List.ofFn v).drop (r.start i)).length := by
    simp only [List.length_drop, List.length_ofFn]
    have := p.isLt
    omega
  apply List.mem_take_iff_getElem.mpr
  refine ⟨p.val - r.start i, by omega, ?_⟩
  rw [List.getElem_drop, List.getElem_ofFn]
  apply congrArg v
  apply Fin.ext
  change r.start i + (p.val - r.start i) = p.val
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition
