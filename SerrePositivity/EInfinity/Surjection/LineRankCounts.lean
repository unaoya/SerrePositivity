module

public import SerrePositivity.EInfinity.Surjection.LineRanks
public import SerrePositivity.EInfinity.Surjection.RawCaesuraOrder
public import Mathlib.Data.Finset.Card

/-!
# 行番号を区切り位置の列で数える

概要：Berger–Fresse §1.2.2・§1.5.7 の行番号を実際の区切り列の先行部分で計算する。
方針：有限集合の区切り数を、重複のない昇順リストの filter の長さに移す。
規約：位置の上界は自然数で、全射性や非退化性を要求しない。
使われ方：成功した table の各選択行の内部で lineRank を行添字へ同定する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

/-- 概要：行番号は指定位置より前の生の区切り列の長さ（BF §1.2.2・§1.5.7）。
方針：filter した区切り列の toFinset を定義の有限集合と同定する。
規約：空語や語長を超える上界も含む。
使われ方：行末位置のリストへ lineRank の計算を移す。 -/
lemma lineRank_eq_rawCaesura_count {n l : ℕ} (v : Fin l → Fin n) (p : ℕ) :
    lineRank v p = ((rawCaesuraList v).filter (fun j => j.val < p)).length := by
  have he : ((rawCaesuraList v).filter (fun j => j.val < p)).toFinset =
      Finset.univ.filter (fun j => j.val < p ∧ Caesura v j) := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, mem_rawCaesuraList,
      decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hn := (rawCaesuraList_sortedLT v).pairwise.nodup.filter (fun j => j.val < p)
  rw [lineRank, ← he, List.toFinset_card_of_nodup hn]

end SerrePositivity.EInfinity.Surjection
