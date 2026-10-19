module

public import SerrePositivity.EInfinity.IntervalCuts.OutputOccurrences
public import SerrePositivity.EInfinity.Surjection.OccurrenceCompleteness

/-!
# 二段区間切断の代入位置の出現分類

概要：Berger–Fresse §2.2.6 の二段切断で、外側の指定出力に対応する語の出現を分類する。
方針：非零切断の左右単射性で出現を左右の二点へ単射し、活動色と辺出力を比較する。
規約：切断点の色は一出現、他の辺出力色は二出現。
使われ方：部分合成の重なる分割を一部分・二部分へ帰着する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：非零な辺切断の各色の出現数は高々二（BF §2.2.1）。
方針：出現位置の切断点以下か以後かで二点へ単射する。
規約：元の語の全射性や非退化性は不要。
使われ方：二段切断の内側分割数を高々二へ絞る。 -/
lemma occurrenceCount_le_two_of_cut {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (h : EdgeNondegenerate u p) (k : Fin n) : occurrenceCount u k ≤ 2 := by
  let side (j : Fin (occurrenceCount u k)) : Fin 2 :=
    if occurrenceAt u k j ≤ p then 0 else 1
  have hi : Function.Injective side := by
    intro i j hij
    apply (occurrenceAt_strictMono u k).injective
    by_cases hi : occurrenceAt u k i ≤ p <;> by_cases hj : occurrenceAt u k j ≤ p
    · exact edge_left_injective h _ _ hi hj
        ((occurrenceAt_value u k i).trans (occurrenceAt_value u k j).symm)
    · simp only [side, ite_eq_left hi, ite_eq_right hj] at hij
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hij)
    · simp only [side, ite_eq_right hi, ite_eq_left hj] at hij
      exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hij)
    · exact edge_right_injective h _ _ (le_of_lt (lt_of_not_ge hi))
        (le_of_lt (lt_of_not_ge hj))
          ((occurrenceAt_value u k i).trans (occurrenceAt_value u k j).symm)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective side hi

/-- 概要：非零切断の切断点色はちょうど一回だけ出現する（BF §2.2.1）。
方針：切断点色の全出現が切断点そのものに一致することを使う。
規約：語は実際の非退化全射基底。
使われ方：内側作用を切断点自身へ代入する唯一分割の分岐。 -/
lemma occurrenceCount_pivot_eq_one {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) : occurrenceCount u.val (u.val p) = 1 := by
  have hp (j : Fin (occurrenceCount u.val (u.val p))) :
      occurrenceAt u.val (u.val p) j = p :=
    pivot_unique h _ (occurrenceAt_value u.val (u.val p) j)
  have hle : occurrenceCount u.val (u.val p) ≤ 1 := by
    by_contra hn
    let i : Fin (occurrenceCount u.val (u.val p)) := ⟨0, by omega⟩
    let j : Fin (occurrenceCount u.val (u.val p)) := ⟨1, by omega⟩
    have he := (occurrenceAt_strictMono u.val (u.val p)).injective ((hp i).trans (hp j).symm)
    have hv := congrArg Fin.val he
    change 0 = 1 at hv
    omega
  have hpos := occurrenceCount_pos u (u.val p)
  omega

/-- 概要：二回出現する色の非零切断の出力は辺（BF §2.2.3）。
方針：最初の二出現の前者は活動位置の区切りとなる。
規約：切断の非退化性から二出現は切断点を跨ぐ。
使われ方：内側の二部分割を辺入力の作用へ対応させる。 -/
lemma edgeOutput_eq_edge_of_two_occurrences {n d : ℕ} (u : BasisWord n d)
    (p : Fin (n + d)) (h : EdgeNondegenerate u.val p) (k : Fin n)
    (hk : occurrenceCount u.val k = 2) : edgeOutput u p k = edge := by
  let i : Fin (occurrenceCount u.val k) := ⟨0, by omega⟩
  let j : Fin (occurrenceCount u.val k) := ⟨1, by omega⟩
  apply (edgeOutput_eq_edge_iff u p h k).mpr
  refine ⟨occurrenceAt u.val k i, Finset.mem_insert.mpr (Or.inr ?_), occurrenceAt_value _ _ _⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, occurrenceAt u.val k j, ?_, ?_⟩
  · exact occurrenceAt_strictMono u.val k (by change 0 < 1; decide)
  · exact (occurrenceAt_value u.val k j).trans (occurrenceAt_value u.val k i).symm

/-- 概要：非零切断の辺出力は切断点色または二出現色に限る（BF §2.2.3）。
方針：活動位置を切断点と区切りに分け、区切りの二出現と出現数上限を使う。
規約：全 arity・全語次数。
使われ方：二段切断の内側辺作用の二つの分岐。 -/
lemma edgeOutput_eq_edge_iff_pivot_or_two {n d : ℕ} (u : BasisWord n d)
    (p : Fin (n + d)) (h : EdgeNondegenerate u.val p) (k : Fin n) :
    edgeOutput u p k = edge ↔ k = u.val p ∨ occurrenceCount u.val k = 2 := by
  constructor
  · intro he
    obtain ⟨i, hi, hik⟩ := (edgeOutput_eq_edge_iff u p h k).mp he
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Or.inl hik.symm
    · obtain ⟨j, hij, hji⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨a, ha⟩ := occurrenceAt_complete u.val k i hik
      obtain ⟨b, hb⟩ := occurrenceAt_complete u.val k j (hji.trans hik)
      have hab : a < b := (occurrenceAt_strictMono u.val k).lt_iff_lt.mp (by rwa [ha, hb])
      have ha0 := a.isLt
      have hb0 := b.isLt
      have hle := occurrenceCount_le_two_of_cut u.val p h k
      have habv := Fin.lt_def.mp hab
      exact Or.inr (by omega)
  · rintro (rfl | hk)
    · exact (edgeOutput_eq_edge_iff u p h _).mpr ⟨p, Finset.mem_insert_self _ _, rfl⟩
    · exact edgeOutput_eq_edge_of_two_occurrences u p h k hk

/-- 概要：非辺の指定出力は切断点以外の一出現色にちょうど対応（BF §2.2.3）。
方針：辺出力の分類と全射性による出現数の正性を組み合わせる。
規約：非辺出力は零頂点か一頂点。
使われ方：内側が頂点へ作用する唯一分割の分岐。 -/
lemma edgeOutput_ne_edge_iff_single_nonpivot {n d : ℕ} (u : BasisWord n d)
    (p : Fin (n + d)) (h : EdgeNondegenerate u.val p) (k : Fin n) :
    edgeOutput u p k ≠ edge ↔ k ≠ u.val p ∧ occurrenceCount u.val k = 1 := by
  have he := edgeOutput_eq_edge_iff_pivot_or_two u p h k
  have hle := occurrenceCount_le_two_of_cut u.val p h k
  have hpos := occurrenceCount_pos u k
  constructor
  · intro hn
    have hnot : ¬(k = u.val p ∨ occurrenceCount u.val k = 2) := fun hk => hn (he.mpr hk)
    exact ⟨fun hk => hnot (Or.inl hk), by omega⟩
  · rintro ⟨hn, h1⟩ hedge
    rcases he.mp hedge with hk | h2
    · exact hn hk
    · omega

end SerrePositivity.EInfinity.IntervalCuts
