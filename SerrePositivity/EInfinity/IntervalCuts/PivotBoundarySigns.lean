module

public import SerrePositivity.EInfinity.IntervalCuts.ActiveRanks

/-!
# 切断点色の境界係数の切断点からの独立性

概要：Berger–Fresse §2.2.7 の切断点色の Koszul 境界係数は全非零切断で共通する。
方針：活動集合から切断点を除くと全区切り集合が残ることを逆転符号公式へ代入する。
規約：係数は元の語の区切り数と区切り色の逆転数だけで決まる。
使われ方：隣接する切断点色の端点項の相殺と両端の削除障害項の比較。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open scoped BigOperators

/-- 概要：非零切断の活動集合から切断点を除くと全区切り集合（BF §2.2.7）。
方針：切断点自身は区切りでないことを使う。
規約：切断点以外の全活動位置を保持する。
使われ方：切断点色の因子境界で残る交換符号を固定する。 -/
lemma activePositions_erase_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : EdgeNondegenerate u p) :
    (activePositions u p).erase p = Finset.univ.filter (Caesura u) := by
  have hp : p ∉ Finset.univ.filter (Caesura u) := by
    intro hp
    exact (lt_irrefl p) (caesura_before_pivot h (Finset.mem_filter.mp hp).2)
  exact Finset.erase_insert hp

/-- 概要：非零切断の切断点の活動順位は全区切り数（BF §2.2.7）。
方針：全区切りが切断点より前にあることを使う。
規約：切断点自身は順位に数えない。
使われ方：切断点色の境界係数の位置符号を固定する。 -/
lemma positionRank_active_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : EdgeNondegenerate u p) :
    positionRank (activePositions u p) p = (Finset.univ.filter (Caesura u)).card := by
  unfold positionRank
  congr 1
  ext i
  simp only [activePositions, Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨rfl | hi, hip⟩
    · exact False.elim ((lt_irrefl _) hip)
    · exact hi
  · intro hi
    exact ⟨Or.inr hi, caesura_before_pivot h hi⟩

/-- 概要：切断点色の出力境界係数は区切り集合だけで決まる（BF §2.2.7）。
方針：活動集合の逆転符号の切断点削除公式と全区切りの順位を使う。
規約：語の次数を限定しない。
使われ方：隣接切断の切断点色の端点項を共通係数で相殺する。 -/
lemma edgeSign_pivot_boundary {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) :
    edgeSign u.val p * (-1 : ℤ) ^
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < u.val p),
          simplexDegree (edgeOutput u p k)) =
      (-1 : ℤ) ^ (Finset.univ.filter (Caesura u.val)).card *
        (-1 : ℤ) ^ positionInversionCount u.val (Finset.univ.filter (Caesura u.val)) := by
  rw [edgeSign_eq_inversionCount h, edgeOutput_prefix_degree u p h]
  have hs := positionInversionSign_erase u.val (activePositions u.val p)
    (activePositions_injOn h) p (Finset.mem_insert_self _ _)
  rw [positionRank_active_pivot h, activePositions_erase_pivot h] at hs
  exact hs

end SerrePositivity.EInfinity.IntervalCuts
