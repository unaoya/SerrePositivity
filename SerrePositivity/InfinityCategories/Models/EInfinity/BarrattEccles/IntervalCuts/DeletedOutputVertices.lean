module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.OutputOccurrences
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletion

/-!
模型。文献の定義との比較は後で
# 文字削除後の切断の出力頂点

概要：Berger–Fresse §2.2.7 の削除項と切断の境界項の出力を比較する。
方針：切断点を残して削除し、元位置の左右の出現を削除の順序単射で比較する。
規約：削除色以外は変わらず、反復色の左出現の削除は一頂点を残す。
使われ方：χ の削除項と出力辺の二端点への置換の値の一致。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：削除色以外の左側の出現は削除の前後で同値（BF §2.2.7）。
方針：順序単射で出現を写し、逆方向は削除位置でない出現を戻す。
規約：切断点の元位置は i.succAbove q。
使われ方：削除色以外の零頂点の保存。 -/
lemma erase_left_occurrence_iff {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (k : Fin n) (hk : k ≠ u i) :
    (∃ a : Fin l, a ≤ q ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i a = k) ↔
      ∃ b : Fin (l + 1), b ≤ i.succAbove q ∧ u b = k := by
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨i.succAbove a, (Fin.strictMono_succAbove i).monotone ha, hu⟩
  · rintro ⟨b, hb, hu⟩
    have hbi : b ≠ i := by intro h; subst b; exact hk hu.symm
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨a, ?_, ?_⟩
    · apply (Fin.strictMono_succAbove i).le_iff_le.mp
      rwa [ha]
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, ha] using hu

/-- 概要：削除色以外の右側の出現は削除の前後で同値（BF §2.2.7）。
方針：削除の順序単射による大小の保存と反映を使う。
規約：切断点を含む右側。
使われ方：削除色以外の一頂点の保存。 -/
lemma erase_right_occurrence_iff {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (k : Fin n) (hk : k ≠ u i) :
    (∃ a : Fin l, q ≤ a ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i a = k) ↔
      ∃ b : Fin (l + 1), i.succAbove q ≤ b ∧ u b = k := by
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨i.succAbove a, (Fin.strictMono_succAbove i).monotone ha, hu⟩
  · rintro ⟨b, hb, hu⟩
    have hbi : b ≠ i := by intro h; subst b; exact hk hu.symm
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨a, ?_, ?_⟩
    · apply (Fin.strictMono_succAbove i).le_iff_le.mp
      rwa [ha]
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, ha] using hu

/-- 概要：削除色以外の出力頂点集合は削除前後で厳密に一致（BF §2.2.7）。
方針：零・一の所属を左右の色の出現へ移して比較する。
規約：語の非退化性は不要。
使われ方：境界の一因子以外のテンソル因子を一致させる。 -/
lemma edgeOutputVertices_erase_of_ne {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (k : Fin n) (hk : k ≠ u i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices u (i.succAbove q) k := by
  apply Finset.ext
  intro b
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_mem_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_mem_iff,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_left_occurrence_iff u i q k hk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_right_occurrence_iff u i q k hk]

/-- 概要：反復色の左出現の削除後、その色の出力は一頂点（BF §2.2.7）。
方針：左側の単射性で零頂点を排除し、別の同色出現が右側に残ることを使う。
規約：削除位置は切断点より厳密に左。
使われ方：出力辺の終点への置換と χ の左出現削除の値の一致。 -/
lemma edgeOutputVertices_erase_left {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (i.succAbove q))
    (hi : i < i.succAbove q) (hr : ∃ j, j ≠ i ∧ u j = u i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q (u i) = {1} := by
  have h0 : (0 : Fin 2) ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q (u i) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zero_mem_edgeOutputVertices_iff]
    rintro ⟨a, ha, hu⟩
    exact Fin.succAbove_ne i a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h _ i
      ((Fin.strictMono_succAbove i).monotone ha) hi.le hu)
  have h1 : (1 : Fin 2) ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q (u i) := by
    obtain ⟨j, hji, huj⟩ := hr
    have hpj : i.succAbove q ≤ j := by
      by_contra hj
      exact hji (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h j i (le_of_lt (lt_of_not_ge hj)) hi.le huj)
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hji
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.one_mem_edgeOutputVertices_iff]
    refine ⟨a, ?_, ?_⟩
    · apply (Fin.strictMono_succAbove i).le_iff_le.mp
      rwa [ha]
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, ha] using huj
  apply Finset.ext
  intro b
  fin_cases b <;> simp [h0, h1]

/-- 概要：反復色の右出現の削除後、その色の出力は零頂点（BF §2.2.7）。
方針：右側の単射性で一頂点を排除し、別の同色出現が左側に残ることを使う。
規約：削除位置は切断点より厳密に右。
使われ方：出力辺の始点への置換と χ の右出現削除の値の一致。 -/
lemma edgeOutputVertices_erase_right {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (i.succAbove q))
    (hi : i.succAbove q < i) (hr : ∃ j, j ≠ i ∧ u j = u i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q (u i) = {0} := by
  have h1 : (1 : Fin 2) ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q (u i) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.one_mem_edgeOutputVertices_iff]
    rintro ⟨a, ha, hu⟩
    exact Fin.succAbove_ne i a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h _ i
      ((Fin.strictMono_succAbove i).monotone ha) hi.le hu)
  have h0 : (0 : Fin 2) ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q (u i) := by
    obtain ⟨j, hji, huj⟩ := hr
    have hjp : j ≤ i.succAbove q := by
      by_contra hj
      exact hji (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h j i (le_of_lt (lt_of_not_ge hj)) hi.le huj)
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hji
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zero_mem_edgeOutputVertices_iff]
    refine ⟨a, ?_, ?_⟩
    · apply (Fin.strictMono_succAbove i).le_iff_le.mp
      rwa [ha]
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, ha] using huj
  apply Finset.ext
  intro b
  fin_cases b <;> simp [h0, h1]

/-- 概要：左出現の削除後の全出力族は、その色を終点へ置換した元の出力族（BF §2.2.7）。
方針：削除色では一頂点、他の色では同じ出力頂点集合であることを使う。
規約：削除前後とも実際の非退化全射基底語。
使われ方：χ の削除項と辺の終点境界項のテンソル値を一致させる。 -/
lemma edgeOutput_eraseCut_left {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val (i.succAbove q)) (hi : i < i.succAbove q)
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.eraseCutBasisWord u (i.succAbove q) i h (ne_of_lt hi) hr) q =
      Function.update (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u (i.succAbove q)) (u.val i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1) := by
  funext k
  by_cases hk : k = u.val i
  · subst k
    rw [Function.update_self]
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_erase_left u.val i q h hi hr
  · rw [Function.update_of_ne hk]
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_erase_of_ne u.val i q k hk

/-- 概要：右出現の削除後の全出力族は、その色を始点へ置換した元の出力族（BF §2.2.7）。
方針：削除色では零頂点、他の色では同じ出力頂点集合であることを使う。
規約：切断点を残し、同色の左出現を残す。
使われ方：χ の削除項と辺の始点境界項のテンソル値を一致させる。 -/
lemma edgeOutput_eraseCut_right {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val (i.succAbove q)) (hi : i.succAbove q < i)
    (hr : ∃ j, j ≠ i ∧ u.val j = u.val i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.eraseCutBasisWord u (i.succAbove q) i h (ne_of_gt hi) hr) q =
      Function.update (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u (i.succAbove q)) (u.val i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0) := by
  funext k
  by_cases hk : k = u.val i
  · subst k
    rw [Function.update_self]
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_erase_right u.val i q h hi hr
  · rw [Function.update_of_ne hk]
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_erase_of_ne u.val i q k hk

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
