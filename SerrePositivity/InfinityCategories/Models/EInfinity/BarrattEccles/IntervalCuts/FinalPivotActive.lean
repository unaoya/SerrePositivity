module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GeneralDeletionActive

/-!
模型。文献の定義との比較は後で
# 最終同色を削除して切断点を残す場合の活動集合

概要：Berger–Fresse §2.2.7 の切断点障害の右削除後の活動集合は元の全区切り集合へ戻る。
方針：最後の同色出現の削除で失う切断点の区切りを、活動集合の切断点として加え直す。
規約：元切断の非零性は仮定しない。
使われ方：右の切断点障害削除係数の実際の交換符号。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：最終同色の削除後、切断点を含む活動集合の像は元の全区切り集合（BF §2.2.7）。
方針：最終出現削除の区切り公式で失う一位置を、切断点として復元する。
規約：切断点が削除色の直前の出現であることを要求する。
使われ方：切断点障害右削除の符号公式。 -/
lemma activePositions_erase_final_pivot_image {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (hi : i.succAbove q < i)
    (hu : u (i.succAbove q) = u i) (hn : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i)
    (hgap : ∀ b, i.succAbove q < b → b < i → u b ≠ u i) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q).image i.succAbove = Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u (i.succAbove q) := ⟨i, hi, hu.symm⟩
  ext b
  simp only [Finset.mem_image, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha | ha, rfl⟩
    · subst a
      exact hp
    · exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_final u _ i hi hu hn hgap a).mp ha).1
  · intro hb
    have hbi : b ≠ i := by rintro rfl; exact hn hb
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨a, ?_, ha⟩
    by_cases hbp : b = i.succAbove q
    · exact Or.inl (Fin.succAbove_right_injective (ha.trans hbp))
    · right
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_final u _ i hi hu hn hgap a).mpr
      simpa only [ha] using And.intro hb hbp

/-- 概要：最終同色削除後の実際の切断符号は元の全区切りの逆転符号（BF §2.2.7）。
方針：非零削除切断の活動集合を元の全区切り集合へ移す。
規約：元切断自身は退化していてよい。
使われ方：右削除項を全区切り集合の共通係数へ比較する。 -/
lemma edgeSign_erase_final_pivot {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (hi : i.succAbove q < i) (hu : u (i.succAbove q) = u i) (hn : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i)
    (hgap : ∀ b, i.succAbove q < b → b < i → u b ≠ u i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_image u i q h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_erase_final_pivot_image u i q hi hu hn hgap]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
