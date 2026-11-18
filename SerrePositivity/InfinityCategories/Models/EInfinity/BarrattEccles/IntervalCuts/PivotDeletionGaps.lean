module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapPivotDeletion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutPartner

/-!
模型。文献の定義との比較は後で
# 切断点障害の非零削除項から隙間への逆対応

概要：Berger–Fresse §2.2.7 の切断点障害の非零削除項は隣接する非退化隙間を定める。
方針：元の同側等色対は削除位置と切断点の対だけであることを使う。
規約：削除位置が元切断点より前か後かで隙間を選ぶ。
使われ方：隙間から構成した削除項との両方向の分類。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：切断点と同色の左位置を消した非零削除項は直前の非退化隙間を定める（BF §2.2.7）。
方針：隙間内の同側同色対があれば元の障害対に等しくなるが、隙間の両側に分離されている。
規約：元の辺切断自体は退化。
使われ方：切断点障害の左削除項を隙間へ分類する。 -/
lemma gap_before_of_erase_pivot {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (hi : i < i.succAbove q) (hu : u i = u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u (i.succAbove q).castSucc := by
  have hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q (i.succAbove q) :=
    ⟨Fin.succAbove_ne i q, hu.symm, Or.inl ⟨hi.le, le_rfl⟩⟩
  constructor
  · intro a b ha hb hab
    have ha' : a < i.succAbove q := ha
    have hb' : b < i.succAbove q := hb
    by_contra hne
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.same_side_equal_pair_is_defect_pair u i q h _ hd a b
      (Or.inl ⟨ha'.le, hb'.le⟩) hab hne with hp | hp
    · exact (ne_of_lt hb') hp.2
    · exact (ne_of_lt ha') hp.1
  · intro a b ha hb hab
    have ha' : i.succAbove q ≤ a := ha
    have hb' : i.succAbove q ≤ b := hb
    by_contra hne
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.same_side_equal_pair_is_defect_pair u i q h _ hd a b
      (Or.inr ⟨ha', hb'⟩) hab hne with hp | hp
    · exact (not_le_of_gt hi) (hp.1 ▸ ha')
    · exact (not_le_of_gt hi) (hp.2 ▸ hb')

/-- 概要：切断点と同色の右位置を消した非零削除項は直後の非退化隙間を定める（BF §2.2.7）。
方針：同側同色対の分類と、削除位置・切断点が隙間で分離されることを使う。
規約：元の辺切断自体は退化。
使われ方：切断点障害の右削除項を隙間へ分類する。 -/
lemma gap_after_of_erase_pivot {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (hi : i.succAbove q < i) (hu : u i = u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u (i.succAbove q).succ := by
  have hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q (i.succAbove q) :=
    ⟨Fin.succAbove_ne i q, hu.symm, Or.inr ⟨hi.le, le_rfl⟩⟩
  constructor
  · intro a b ha hb hab
    have ha' : a ≤ i.succAbove q := Nat.le_of_lt_add_one ha
    have hb' : b ≤ i.succAbove q := Nat.le_of_lt_add_one hb
    by_contra hne
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.same_side_equal_pair_is_defect_pair u i q h _ hd a b
      (Or.inl ⟨ha', hb'⟩) hab hne with hp | hp
    · exact (not_le_of_gt hi) (hp.1 ▸ ha')
    · exact (not_le_of_gt hi) (hp.2 ▸ hb')
  · intro a b ha hb hab
    have ha' : i.succAbove q < a := Nat.lt_of_add_one_le ha
    have hb' : i.succAbove q < b := Nat.lt_of_add_one_le hb
    by_contra hne
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.same_side_equal_pair_is_defect_pair u i q h _ hd a b
      (Or.inr ⟨ha'.le, hb'.le⟩) hab hne with hp | hp
    · exact (ne_of_gt hb') hp.2
    · exact (ne_of_gt ha') hp.1

/-- 概要：切断点同色の左削除後の非零性は元の直前隙間の非退化性と同値（BF §2.2.7）。
方針：削除の構成と逆対応を組み合わせる。
規約：同色条件と左右の順序だけを固定する。
使われ方：隙間による削除和の添字替え。 -/
lemma erase_pivot_iff_gap_before {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (hi : i < i.succAbove q)
    (hu : u i = u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u (i.succAbove q).castSucc :=
  ⟨fun h => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gap_before_of_erase_pivot u i q h hi hu,
    fun h => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate_of_gap_before u i q h hi hu⟩

/-- 概要：切断点同色の右削除後の非零性は元の直後隙間の非退化性と同値（BF §2.2.7）。
方針：削除の構成と逆対応を組み合わせる。
規約：同色条件と左右の順序だけを固定する。
使われ方：隙間による削除和の添字替え。 -/
lemma erase_pivot_iff_gap_after {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (hi : i.succAbove q < i)
    (hu : u i = u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u (i.succAbove q).succ :=
  ⟨fun h => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gap_after_of_erase_pivot u i q h hi hu,
    fun h => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_edgeNondegenerate_of_gap_after u i q h hi hu⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
