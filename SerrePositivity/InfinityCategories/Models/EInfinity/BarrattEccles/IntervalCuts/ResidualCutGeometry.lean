module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutInvolution
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ActiveRanks

/-!
模型。文献の定義との比較は後で
# 非切断点障害の同色位置と元切断点の順位

概要：Berger–Fresse §2.2.7 の交換対では二つの同色位置は同色の出現順でも隣り合う。
方針：間の同色位置があれば障害位置の一意性に矛盾することを使う。
規約：元の切断点の色は削除色と異なり、元の切断点は区切りではない。
使われ方：一般の削除符号公式と活動位置の逆転符号を交換対へ適用する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非切断点障害の交換対では元切断点の色は削除色と異なる（BF §2.2.7）。
方針：同じ色なら切断点自身も障害位置となり、一意性に矛盾する。
規約：元切断は退化していてよい。
使われ方：元切断点が活動集合への新たな一点であることを示す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.pivot_color_ne {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) : u (c.deleted.succAbove c.pivot) ≠ u c.deleted := by
  intro he
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (c.deleted.succAbove c.pivot) c.deleted
      (c.deleted.succAbove c.pivot) := by
    rcases le_total c.deleted (c.deleted.succAbove c.pivot) with h | h
    · exact Or.inl ⟨h, le_rfl⟩
    · exact Or.inr ⟨h, le_rfl⟩
  have hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u c.deleted c.pivot (c.deleted.succAbove c.pivot) :=
    ⟨Fin.succAbove_ne c.deleted c.pivot, he, hs⟩
  exact c.defect_ne_pivot (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cutDeletionDefect_unique u c.deleted c.pivot c.nondegenerate
    c.defect _ c.defect_spec hp)

/-- 概要：非切断点障害の元切断点は区切りではない（BF §2.2.7）。
方針：後の同色位置があれば削除後の右側の単射性に矛盾する。
規約：削除位置と同色の場合は切断点色の不一致で排除する。
使われ方：切断点を活動集合へ挿入した際の順位補正。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.pivot_not_caesura {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u (c.deleted.succAbove c.pivot) := by
  rintro ⟨k, hpk, huk⟩
  by_cases hki : k = c.deleted
  · subst k
    exact c.pivot_color_ne huk.symm
  · have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_same_side_injective u c.deleted c.pivot c.nondegenerate
      (c.deleted.succAbove c.pivot) k (Fin.succAbove_ne c.deleted c.pivot) hki
      (Or.inr ⟨le_rfl, hpk.le⟩) huk.symm
    exact (ne_of_lt hpk) he

/-- 概要：順序付けた交換二位置の間には同色位置がない（BF §2.2.7）。
方針：間の同色位置も同じ側にあり、障害の一意性に矛盾する。
規約：他色の位置は何個あってもよい。
使われ方：三回以上の同色も許す一般の逆転符号と最終出現削除へ適用する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.same_color_gap {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) :
    ∀ k, c.deleted < k → k < c.defect → u k ≠ u c.defect := by
  intro k hik hkj huk
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (c.deleted.succAbove c.pivot) c.deleted k := by
    rcases c.defect_spec.2.2 with hs | hs
    · exact Or.inl ⟨hs.1, le_trans hkj.le hs.2⟩
    · exact Or.inr ⟨hs.1, le_trans hs.1 hik.le⟩
  have hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u c.deleted c.pivot k :=
    ⟨ne_of_gt hik, huk.trans c.defect_spec.2.1, hs⟩
  exact (ne_of_lt hkj) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cutDeletionDefect_unique u c.deleted c.pivot c.nondegenerate
    k c.defect hk c.defect_spec)

/-- 概要：切断点以下の位置では活動順位と区切り順位が等しい（BF §2.2.7）。
方針：前方位置のフィルタには追加した切断点が入らないことを使う。
規約：元切断の非零性は不要。
使われ方：左側交換対の削除係数を位置順位へ直す。 -/
lemma positionRank_active_left {n l : ℕ} (u : Fin l → Fin n) (p a : Fin l) (ha : a ≤ p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p) a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u a := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank, Finset.filter_insert,
    not_lt_of_ge ha, Finset.filter_filter, and_comm]

/-- 概要：区切りでない切断点より後の活動順位は区切り順位+1（BF §2.2.7）。
方針：前方の活動集合へ切断点が一つ加わることを数える。
規約：切断点が区切りでない証明を要求する。
使われ方：右側交換対に共通する符号補正を取り出す。 -/
lemma positionRank_active_right {n l : ℕ} (u : Fin l → Fin n) (p a : Fin l)
    (ha : p < a) (hp : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p) a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u a + 1 := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank, Finset.filter_insert,
    ha, hp, Finset.filter_filter, and_comm]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
