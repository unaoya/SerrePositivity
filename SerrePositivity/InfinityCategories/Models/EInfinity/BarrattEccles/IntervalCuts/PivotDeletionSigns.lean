module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapCaesuraRanks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FinalPivotActive
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionDuplicates
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotDeletionGaps

/-!
模型。文献の定義との比較は後で
# 切断点障害の削除項の一般係数公式

概要：Berger–Fresse §2.2.7 の切断点同色削除係数を元の全区切り集合の共通係数へ同定する。
方針：左削除は同色位置の逆転数公式、右削除は最後の区切り順位と活動集合の復元を使う。
規約：左削除は共通係数の負、右削除は共通係数自身となる。
使われ方：隙間ごとの切断点障害削除和と辺切断境界和の比較。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：切断点同色の左削除係数は全区切り共通係数の負（BF §2.2.7）。
方針：同色位置を一つずつ除く逆転符号公式を使い、切断点を除くと全区切り集合へ戻す。
規約：元の辺切断の存在を仮定しない。
使われ方：隙間右隣の退化切断から来る削除項の係数。 -/
lemma pivotDeletion_coefficient_before {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (hi : i < i.succAbove q) (hu : u i = u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u i * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q =
      -((-1 : ℤ) ^ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u)).card *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u))) := by
  have hg := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gap_before_of_erase_pivot u i q h hi hu
  have hic : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i := ⟨i.succAbove q, hi, hu.symm⟩
  have hp : i.succAbove q ∉ Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u) := by
    intro hp
    exact (lt_irrefl _) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_gap_pivot hg (Finset.mem_filter.mp hp).2)
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionSign_erase_same_color u (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q))
    i (i.succAbove q)
    (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hic⟩))
    (Finset.mem_insert_self _ _) hi hu (by
      intro j _ hij hjp huj
      exact (ne_of_gt hij) (hg.1 j i hjp hi (huj.trans hu.symm)))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_active_left u _ _ hi.le, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_gap_pivot hg,
    show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)).erase (i.succAbove q) =
      Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u) from Finset.erase_insert hp] at hs
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura u i hic, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_caesura u i q h hic]
  exact hs

/-- 概要：切断点同色の右削除係数は全区切り共通係数自身（BF §2.2.7）。
方針：最後の同色削除で符号を反転し、切断点区切りの順位+1と全区切り数を一致させる。
規約：元の非零辺切断がない場合も含む。
使われ方：隙間左隣の退化切断から来る削除項の係数。 -/
lemma pivotDeletion_coefficient_after {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (hi : i.succAbove q < i) (hu : u i = u (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u i * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q =
      (-1 : ℤ) ^ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u)).card *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u)) := by
  have hg := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gap_after_of_erase_pivot u i q h hi hu
  have hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u (i.succAbove q) := ⟨i, hi, hu⟩
  have hn : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i := fun hic => (not_le_of_gt hi) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_le_gap_pivot hg hic)
  have hgap : ∀ b, i.succAbove q < b → b < i → u b ≠ u i := by
    intro b hpb hbi hub
    exact (ne_of_lt hbi) (hg.2 b i (Nat.add_one_le_of_lt hpb)
      (Nat.add_one_le_of_lt hi) hub)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.deletionCoefficient_final_gap u _ i hi hu.symm hn hgap,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura u _ hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_final_pivot u i q h hi hu.symm hn hgap,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesuraRank_gap_pivot hg hp, pow_succ, mul_neg_one]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
