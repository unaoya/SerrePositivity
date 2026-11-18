module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionDeletion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.OutputOccurrences
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceBoundaries
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionSigns

/-!
模型。文献の定義との比較は後で
# 活動位置の順位と切断の境界符号

概要：Berger–Fresse §2.2.7 の削除位置順位と出力辺の次数順位を同定する。
方針：活動位置の切断点を除いた部分は区切りであり、活動色は出力辺と単射に対応する。
規約：非零切断だけを扱い、色順の順位は全ての出力因子の次数和で表す。
使われ方：逆転数の削除公式を χ の削除係数へ接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：区切りの活動集合内の順位は元の区切り順位（BF §2.2.7）。
方針：切断点は指定区切りより後なので、前方の活動位置は区切りだけ。
規約：切断点自身はこの順位に入らない。
使われ方：逆転数の位置順位を削除係数へ置き換える。 -/
lemma positionRank_active_caesura {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (a : Fin l) (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p) a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u a := by
  have hap := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot h ha
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank
  congr 1
  ext j
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
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
lemma simplexDegree_eq_edge_indicator (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s = if s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge then 1 else 0 := by
  have hv (b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge := by
    intro he
    have hd := congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree he
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_edge] at hd
    exact Nat.zero_ne_one hd
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplex_cases s with rfl | rfl | rfl <;> simp [hv]

/-- 概要：指定色より前の出力次数和は活動色の順位（BF §2.2.7）。
方針：辺の色の集合を活動位置の色の像に同定し、その単射性で個数を保つ。
規約：指定色は活動色でなくてもよい。
使われ方：テンソルの Koszul 境界符号を色順位へ置き換える。 -/
lemma edgeOutput_prefix_degree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (k : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p j)) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).filter (fun i => u.val i < k)).card := by
  have hs : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).filter (fun i => u.val i < k)).image u.val =
      Finset.univ.filter (fun j : Fin n => j < k ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p j = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u p h]
    constructor
    · rintro ⟨i, ⟨hi, hik⟩, rfl⟩
      exact ⟨hik, i, hi, rfl⟩
    · rintro ⟨hjk, i, hi, rfl⟩
      exact ⟨i, ⟨hi, hjk⟩, rfl⟩
  have hc : (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).filter (fun i => u.val i < k)).image u.val).card =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).filter (fun i => u.val i < k)).card :=
    Finset.card_image_of_injOn (fun i hi j hj hij =>
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_injOn h (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij)
  rw [hs] at hc
  simp_rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_eq_edge_indicator]
  rw [Finset.sum_boole, Finset.filter_filter]
  exact hc

/-- 概要：反復色の最初の出現の削除係数と出力境界符号は交換符号で結ばれる（BF §2.2.7）。
方針：活動集合の一位置削除公式へ、区切り順位と出力次数順位の一致を代入する。
規約：右辺の交換指数は元の活動集合からその区切りを除いたもの。
使われ方：削除後の実際の活動集合へ移す前の符号比較。 -/
lemma edgeSign_caesura_boundary {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p a : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p * (-1 : ℤ) ^
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < u.val a),
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val a *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).erase a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_prefix_degree u p h,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura u.val a ha]
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionSign_erase u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_injOn h) a (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank_active_caesura h a ha] at hs
  exact hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
