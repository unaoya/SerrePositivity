module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ActiveRanks

/-!
模型。文献の定義との比較は後で
# 切断点色の境界係数の切断点からの独立性

概要：Berger–Fresse §2.2.7 の切断点色の Koszul 境界係数は全非零切断で共通する。
方針：活動集合から切断点を除くと全区切り集合が残ることを逆転符号公式へ代入する。
規約：係数は元の語の区切り数と区切り色の逆転数だけで決まる。
使われ方：隣接する切断点色の端点項の相殺と両端の削除障害項の比較。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：非零切断の活動集合から切断点を除くと全区切り集合（BF §2.2.7）。
方針：切断点自身は区切りでないことを使う。
規約：切断点以外の全活動位置を保持する。
使われ方：切断点色の因子境界で残る交換符号を固定する。 -/
lemma activePositions_erase_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p).erase p = Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u) := by
  have hp : p ∉ Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u) := by
    intro hp
    exact (lt_irrefl p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot h (Finset.mem_filter.mp hp).2)
  exact Finset.erase_insert hp

/-- 概要：非零切断の切断点の活動順位は全区切り数（BF §2.2.7）。
方針：全区切りが切断点より前にあることを使う。
規約：切断点自身は順位に数えない。
使われ方：切断点色の境界係数の位置符号を固定する。 -/
lemma positionRank_active_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p) p = (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u)).card := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank
  congr 1
  ext i
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨rfl | hi, hip⟩
    · exact False.elim ((lt_irrefl _) hip)
    · exact hi
  · intro hi
    exact ⟨Or.inr hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot h hi⟩

/-- 概要：切断点色の出力境界係数は区切り集合だけで決まる（BF §2.2.7）。
方針：活動集合の逆転符号の切断点削除公式と全区切りの順位を使う。
規約：語の次数を限定しない。
使われ方：隣接切断の切断点色の端点項を共通係数で相殺する。 -/
lemma edgeSign_pivot_boundary {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p * (-1 : ℤ) ^
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < u.val p),
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k)) =
      (-1 : ℤ) ^ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)).card *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_prefix_degree u p h]
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionSign_erase u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_injOn h) p (Finset.mem_insert_self _ _)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_active_pivot h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_erase_pivot h] at hs
  exact hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
