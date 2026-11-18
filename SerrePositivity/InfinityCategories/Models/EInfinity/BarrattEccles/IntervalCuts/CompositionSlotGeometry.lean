module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.OutputOccurrences
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceCompleteness

/-!
模型。文献の定義との比較は後で
# 二段区間切断の代入位置の出現分類

概要：Berger–Fresse §2.2.6 の二段切断で、外側の指定出力に対応する語の出現を分類する。
方針：非零切断の左右単射性で出現を左右の二点へ単射し、活動色と辺出力を比較する。
規約：切断点の色は一出現、他の辺出力色は二出現。
使われ方：部分合成の重なる分割を一部分・二部分へ帰着する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非零な辺切断の各色の出現数は高々二（BF §2.2.1）。
方針：出現位置の切断点以下か以後かで二点へ単射する。
規約：元の語の全射性や非退化性は不要。
使われ方：二段切断の内側分割数を高々二へ絞る。 -/
lemma occurrenceCount_le_two_of_cut {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (k : Fin n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u k ≤ 2 := by
  let side (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u k)) : Fin 2 :=
    if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u k j ≤ p then 0 else 1
  have hi : Function.Injective side := by
    intro i j hij
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono u k).injective
    by_cases hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u k i ≤ p <;> by_cases hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u k j ≤ p
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h _ _ hi hj
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u k i).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u k j).symm)
    · simp only [side, ite_eq_left hi, ite_eq_right hj] at hij
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hij)
    · simp only [side, ite_eq_right hi, ite_eq_left hj] at hij
      exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hij)
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h _ _ (le_of_lt (lt_of_not_ge hi))
        (le_of_lt (lt_of_not_ge hj))
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u k i).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u k j).symm)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective side hi

/-- 概要：非零切断の切断点色はちょうど一回だけ出現する（BF §2.2.1）。
方針：切断点色の全出現が切断点そのものに一致することを使う。
規約：語は実際の非退化全射基底。
使われ方：内側作用を切断点自身へ代入する唯一分割の分岐。 -/
lemma occurrenceCount_pivot_eq_one {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val (u.val p) = 1 := by
  have hp (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val (u.val p))) :
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val (u.val p) j = p :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique h _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val (u.val p) j)
  have hle : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val (u.val p) ≤ 1 := by
    by_contra hn
    let i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val (u.val p)) := ⟨0, by omega⟩
    let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val (u.val p)) := ⟨1, by omega⟩
    have he := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono u.val (u.val p)).injective ((hp i).trans (hp j).symm)
    have hv := congrArg Fin.val he
    change 0 = 1 at hv
    omega
  have hpos := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u (u.val p)
  omega

/-- 概要：二回出現する色の非零切断の出力は辺（BF §2.2.3）。
方針：最初の二出現の前者は活動位置の区切りとなる。
規約：切断の非退化性から二出現は切断点を跨ぐ。
使われ方：内側の二部分割を辺入力の作用へ対応させる。 -/
lemma edgeOutput_eq_edge_of_two_occurrences {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (p : Fin (n + d)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (k : Fin n)
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge := by
  let i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨0, by omega⟩
  let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) := ⟨1, by omega⟩
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u p h k).mpr
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i, Finset.mem_insert.mpr (Or.inr ?_), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value _ _ _⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono u.val k (by change 0 < 1; decide)
  · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k j).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_value u.val k i).symm

/-- 概要：非零切断の辺出力は切断点色または二出現色に限る（BF §2.2.3）。
方針：活動位置を切断点と区切りに分け、区切りの二出現と出現数上限を使う。
規約：全 arity・全語次数。
使われ方：二段切断の内側辺作用の二つの分岐。 -/
lemma edgeOutput_eq_edge_iff_pivot_or_two {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (p : Fin (n + d)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (k : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge ↔ k = u.val p ∨ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 2 := by
  constructor
  · intro he
    obtain ⟨i, hi, hik⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u p h k).mp he
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Or.inl hik.symm
    · obtain ⟨j, hij, hji⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_complete u.val k i hik
      obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_complete u.val k j (hji.trans hik)
      have hab : a < b := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono u.val k).lt_iff_lt.mp (by rwa [ha, hb])
      have ha0 := a.isLt
      have hb0 := b.isLt
      have hle := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceCount_le_two_of_cut u.val p h k
      have habv := Fin.lt_def.mp hab
      exact Or.inr (by omega)
  · rintro (rfl | hk)
    · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u p h _).mpr ⟨p, Finset.mem_insert_self _ _, rfl⟩
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_of_two_occurrences u p h k hk

/-- 概要：非辺の指定出力は切断点以外の一出現色にちょうど対応（BF §2.2.3）。
方針：辺出力の分類と全射性による出現数の正性を組み合わせる。
規約：非辺出力は零頂点か一頂点。
使われ方：内側が頂点へ作用する唯一分割の分岐。 -/
lemma edgeOutput_ne_edge_iff_single_nonpivot {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (p : Fin (n + d)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (k : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge ↔ k ≠ u.val p ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1 := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff_pivot_or_two u p h k
  have hle := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrenceCount_le_two_of_cut u.val p h k
  have hpos := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k
  constructor
  · intro hn
    have hnot : ¬(k = u.val p ∨ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 2) := fun hk => hn (he.mpr hk)
    exact ⟨fun hk => hnot (Or.inl hk), by omega⟩
  · rintro ⟨hn, h1⟩ hedge
    rcases he.mp hedge with hk | h2
    · exact hn hk
    · omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
