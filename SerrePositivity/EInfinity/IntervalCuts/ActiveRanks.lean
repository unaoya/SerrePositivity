module

public import SerrePositivity.EInfinity.IntervalCuts.InversionDeletion
public import SerrePositivity.EInfinity.IntervalCuts.OutputOccurrences
public import SerrePositivity.EInfinity.IntervalCuts.FaceBoundaries
public import SerrePositivity.EInfinity.Surjection.DeletionSigns

/-!
# 活動位置の順位と切断の境界符号

概要：Berger–Fresse §2.2.7 の削除位置順位と出力辺の次数順位を同定する。
方針：活動位置の切断点を除いた部分は区切りであり、活動色は出力辺と単射に対応する。
規約：非零切断だけを扱い、色順の順位は全ての出力因子の次数和で表す。
使われ方：逆転数の削除公式を χ の削除係数へ接続する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open scoped BigOperators

/-- 概要：区切りの活動集合内の順位は元の区切り順位（BF §2.2.7）。
方針：切断点は指定区切りより後なので、前方の活動位置は区切りだけ。
規約：切断点自身はこの順位に入らない。
使われ方：逆転数の位置順位を削除係数へ置き換える。 -/
lemma positionRank_active_caesura {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : EdgeNondegenerate u p) (a : Fin l) (ha : Caesura u a) :
    positionRank (activePositions u p) a = caesuraRank u a := by
  have hap := caesura_before_pivot h ha
  unfold positionRank caesuraRank
  congr 1
  ext j
  simp only [activePositions, Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hj | hj, hja⟩
    · subst j
      exact False.elim ((not_lt_of_ge hap.le) hja)
    · exact ⟨hja, hj⟩
  · rintro ⟨hja, hj⟩
    exact ⟨Or.inr hj, hja⟩

/-- 概要：区間の面の次数は辺なら一、それ以外なら零（BF §2.2.3）。
方針：非退化な面の三分類で次数を計算する。
規約：零・一の頂点と辺のみ。
使われ方：出力因子の次数和を辺の色の個数へ直す。 -/
lemma simplexDegree_eq_edge_indicator (s : Simplex) :
    simplexDegree s = if s = edge then 1 else 0 := by
  have hv (b : Fin 2) : vertex b ≠ edge := by
    intro he
    have hd := congrArg simplexDegree he
    simp only [simplexDegree_vertex, simplexDegree_edge] at hd
    exact Nat.zero_ne_one hd
  rcases simplex_cases s with rfl | rfl | rfl <;> simp [hv]

/-- 概要：指定色より前の出力次数和は活動色の順位（BF §2.2.7）。
方針：辺の色の集合を活動位置の色の像に同定し、その単射性で個数を保つ。
規約：指定色は活動色でなくてもよい。
使われ方：テンソルの Koszul 境界符号を色順位へ置き換える。 -/
lemma edgeOutput_prefix_degree {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) (k : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k), simplexDegree (edgeOutput u p j)) =
      ((activePositions u.val p).filter (fun i => u.val i < k)).card := by
  have hs : ((activePositions u.val p).filter (fun i => u.val i < k)).image u.val =
      Finset.univ.filter (fun j : Fin n => j < k ∧ edgeOutput u p j = edge) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      edgeOutput_eq_edge_iff u p h]
    constructor
    · rintro ⟨i, ⟨hi, hik⟩, rfl⟩
      exact ⟨hik, i, hi, rfl⟩
    · rintro ⟨hjk, i, hi, rfl⟩
      exact ⟨i, ⟨hi, hjk⟩, rfl⟩
  have hc : (((activePositions u.val p).filter (fun i => u.val i < k)).image u.val).card =
      ((activePositions u.val p).filter (fun i => u.val i < k)).card :=
    Finset.card_image_of_injOn (fun i hi j hj hij =>
      activePositions_injOn h (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij)
  rw [hs] at hc
  simp_rw [simplexDegree_eq_edge_indicator]
  rw [Finset.sum_boole, Finset.filter_filter]
  exact hc

/-- 概要：反復色の最初の出現の削除係数と出力境界符号は交換符号で結ばれる（BF §2.2.7）。
方針：活動集合の一位置削除公式へ、区切り順位と出力次数順位の一致を代入する。
規約：右辺の交換指数は元の活動集合からその区切りを除いたもの。
使われ方：削除後の実際の活動集合へ移す前の符号比較。 -/
lemma edgeSign_caesura_boundary {n d : ℕ} (u : BasisWord n d) (p a : Fin (n + d))
    (h : EdgeNondegenerate u.val p) (ha : Caesura u.val a) :
    edgeSign u.val p * (-1 : ℤ) ^
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < u.val a),
          simplexDegree (edgeOutput u p k)) =
      deletionCoefficient u.val a *
        (-1 : ℤ) ^ positionInversionCount u.val ((activePositions u.val p).erase a) := by
  rw [edgeSign_eq_inversionCount h, edgeOutput_prefix_degree u p h,
    deletionCoefficient_of_caesura u.val a ha]
  have hs := positionInversionSign_erase u.val (activePositions u.val p)
    (activePositions_injOn h) a (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)))
  rw [positionRank_active_caesura h a ha] at hs
  exact hs

end SerrePositivity.EInfinity.IntervalCuts
