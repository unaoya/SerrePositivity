module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapValidity
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletion

/-!
模型。文献の定義との比較は後で
# 隙間の隣接退化切断と一意な同色削除

概要：Berger–Fresse §2.2.7 の切断点障害を、非退化な隙間に隣接する退化辺切断から構成する。
方針：反対側の一意な同色位置を削除すると切断点を両側へ含めても単射となる。
規約：元の非零辺切断の存在は仮定しない。
使われ方：切断点障害の全削除和を隙間ごとの和へ変換する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非退化隙間の右隣が退化なら左側に一意な切断点同色位置（BF §2.2.7）。
方針：辺切断の非零性の左同色不在条件を否定し、隙間左側の単射性を使う。
規約：切断点自身は削除しない。
使われ方：左の同色位置を削除する切断点障害項の復元。 -/
lemma gap_before_defect_existsUnique {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.castSucc) (he : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) :
    ∃! i, i < p ∧ u i = u p := by
  have hex : ∃ i, i < p ∧ u i = u p := by
    by_contra hn
    apply he
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff_gap_before u p h).mpr
    intro i hi hu
    exact hn ⟨i, hi, hu⟩
  obtain ⟨i, hi, hu⟩ := hex
  refine ⟨i, ⟨hi, hu⟩, ?_⟩
  intro j hj
  exact h.1 j i hj.1 hi (hj.2.trans hu.symm)

/-- 概要：非退化隙間の左隣が退化なら右側に一意な切断点同色位置（BF §2.2.7）。
方針：辺切断の非零性の右同色不在条件を否定し、隙間右側の単射性を使う。
規約：切断点自身は削除しない。
使われ方：右の同色位置を削除する切断点障害項の復元。 -/
lemma gap_after_defect_existsUnique {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.succ) (he : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) :
    ∃! i, p < i ∧ u i = u p := by
  have hex : ∃ i, p < i ∧ u i = u p := by
    by_contra hn
    apply he
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff_gap_after u p h).mpr
    intro i hi hu
    exact hn ⟨i, hi, hu⟩
  obtain ⟨i, hi, hu⟩ := hex
  refine ⟨i, ⟨hi, hu⟩, ?_⟩
  intro j hj
  exact h.2 j i (Nat.add_one_le_of_lt hj.1) (Nat.add_one_le_of_lt hi) (hj.2.trans hu.symm)

/-- 概要：非退化な直前隙間の左同色を削除すると辺切断は非零（BF §2.2.7）。
方針：左側へ加わる切断点との色衝突は削除位置だけであることを使う。
規約：削除後の切断位置 q の像で元切断点を指定する。
使われ方：隙間の右隣退化から実際の非零削除項を構成する。 -/
lemma erase_edgeNondegenerate_of_gap_before {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u (i.succAbove q).castSucc)
    (hi : i < i.succAbove q) (hu : u i = u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q := by
  have hleft (a b : Fin (l + 1)) (ha : a ≤ i.succAbove q) (hb : b ≤ i.succAbove q)
      (hai : a ≠ i) (hbi : b ≠ i) (hab : u a = u b) : a = b := by
    by_cases hap : a = i.succAbove q
    · subst a
      by_cases hbp : b = i.succAbove q
      · exact hbp.symm
      · have hb' : b < i.succAbove q := lt_of_le_of_ne hb hbp
        exact False.elim (hbi (h.1 b i hb' hi (hab.symm.trans hu.symm)))
    · by_cases hbp : b = i.succAbove q
      · subst b
        have ha' : a < i.succAbove q := lt_of_le_of_ne ha hap
        exact False.elim (hai (h.1 a i ha' hi (hab.trans hu.symm)))
      · have ha' : a < i.succAbove q := lt_of_le_of_ne ha hap
        have hb' : b < i.succAbove q := lt_of_le_of_ne hb hbp
        exact h.1 a b ha' hb' hab
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff]
  constructor
  · intro a b ha hb hab
    apply (Fin.succAbove_right_injective (p := i))
    exact hleft _ _ ((Fin.strictMono_succAbove i).monotone ha)
      ((Fin.strictMono_succAbove i).monotone hb) (Fin.succAbove_ne i a) (Fin.succAbove_ne i b) hab
  · intro a b ha hb hab
    apply (Fin.succAbove_right_injective (p := i))
    exact h.2 _ _ ((Fin.strictMono_succAbove i).monotone ha)
      ((Fin.strictMono_succAbove i).monotone hb) hab

/-- 概要：非退化な直後隙間の右同色を削除すると辺切断は非零（BF §2.2.7）。
方針：右側へ加わる切断点との色衝突は削除位置だけであることを使う。
規約：削除後の切断位置 q の像で元切断点を指定する。
使われ方：隙間の左隣退化から実際の非零削除項を構成する。 -/
lemma erase_edgeNondegenerate_of_gap_after {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u (i.succAbove q).succ)
    (hi : i.succAbove q < i) (hu : u i = u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q := by
  have hright (a b : Fin (l + 1)) (ha : i.succAbove q ≤ a) (hb : i.succAbove q ≤ b)
      (hai : a ≠ i) (hbi : b ≠ i) (hab : u a = u b) : a = b := by
    by_cases hap : a = i.succAbove q
    · subst a
      by_cases hbp : b = i.succAbove q
      · exact hbp.symm
      · have hb' : i.succAbove q < b := lt_of_le_of_ne hb (Ne.symm hbp)
        exact False.elim (hbi (h.2 b i (Nat.add_one_le_of_lt hb')
          (Nat.add_one_le_of_lt hi) (hab.symm.trans hu.symm)))
    · by_cases hbp : b = i.succAbove q
      · subst b
        have ha' : i.succAbove q < a := lt_of_le_of_ne ha (Ne.symm hap)
        exact False.elim (hai (h.2 a i (Nat.add_one_le_of_lt ha')
          (Nat.add_one_le_of_lt hi) (hab.trans hu.symm)))
      · have ha' : i.succAbove q < a := lt_of_le_of_ne ha (Ne.symm hap)
        have hb' : i.succAbove q < b := lt_of_le_of_ne hb (Ne.symm hbp)
        exact h.2 a b (Nat.add_one_le_of_lt ha') (Nat.add_one_le_of_lt hb') hab
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff]
  constructor
  · intro a b ha hb hab
    apply (Fin.succAbove_right_injective (p := i))
    apply h.1 _ _ ?_ ?_ hab
    · exact Nat.lt_add_one_of_le ((Fin.strictMono_succAbove i).monotone ha)
    · exact Nat.lt_add_one_of_le ((Fin.strictMono_succAbove i).monotone hb)
  · intro a b ha hb hab
    apply (Fin.succAbove_right_injective (p := i))
    exact hright _ _ ((Fin.strictMono_succAbove i).monotone ha)
      ((Fin.strictMono_succAbove i).monotone hb) (Fin.succAbove_ne i a) (Fin.succAbove_ne i b) hab

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
