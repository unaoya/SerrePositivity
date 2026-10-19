module

public import SerrePositivity.EInfinity.IntervalCuts.ActiveSigns
public import SerrePositivity.EInfinity.IntervalCuts.Values
public import Mathlib.Tactic.FinCases

/-!
# 切断の出力頂点と元の語の出現

概要：Berger–Fresse §2.2.1 の出力頂点を左右の色の出現で特徴付ける。
方針：展開位置を左右の元位置へ戻し、出力辺を区切りか切断点の色に対応させる。
規約：集合による出力は退化項でも定義でき、辺の対応には非退化性を使う。
使われ方：出力辺の境界項と元の二つの削除位置を結ぶ。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：出力頂点の所属は左右の同色出現で決まる（BF §2.2.1）。
方針：展開位置を左の零頂点と右の一頂点へ分ける。
規約：元の語の全射性や非退化性を仮定しない。
使われ方：出力単体の頂点を削除前後で照合する。 -/
lemma edgeOutputVertices_mem_iff {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (k : Fin n) (b : Fin 2) : b ∈ edgeOutputVertices u p k ↔
      (b = 0 ∧ ∃ i : Fin l, i ≤ p ∧ u i = k) ∨
      (b = 1 ∧ ∃ i : Fin l, p ≤ i ∧ u i = k) := by
  rw [edgeOutputVertices, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hv⟩
    have hq' : edgeLabel u p q = k := (Finset.mem_filter.mp hq).2
    rcases edgePosition_cases p q with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · have he := edgePair_castSucc u p i hi
      exact Or.inl ⟨hv.symm.trans (congrArg Prod.snd he), i, hi,
        (congrArg Prod.fst he).symm.trans hq'⟩
    · have he := edgePair_succ u p i hi
      exact Or.inr ⟨hv.symm.trans (congrArg Prod.snd he), i, hi,
        (congrArg Prod.fst he).symm.trans hq'⟩
  · rintro (⟨rfl, i, hi, hu⟩ | ⟨rfl, i, hi, hu⟩)
    · have he := edgePair_castSucc u p i hi
      exact ⟨i.castSucc, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (congrArg Prod.fst he).trans hu⟩, congrArg Prod.snd he⟩
    · have he := edgePair_succ u p i hi
      exact ⟨i.succ, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (congrArg Prod.fst he).trans hu⟩, congrArg Prod.snd he⟩

/-- 概要：出力に零頂点が現れるのは切断点以下にその色があるとき（BF §2.2.1）。
方針：一般の頂点所属の特徴付けを零へ特殊化する。
規約：切断点を含む。
使われ方：出力の始点を元の左側出現へ戻す。 -/
lemma zero_mem_edgeOutputVertices_iff {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) (k : Fin n) :
    0 ∈ edgeOutputVertices u p k ↔ ∃ i : Fin l, i ≤ p ∧ u i = k := by
  simpa using edgeOutputVertices_mem_iff u p k 0

/-- 概要：出力に一頂点が現れるのは切断点以上にその色があるとき（BF §2.2.1）。
方針：一般の頂点所属の特徴付けを一へ特殊化する。
規約：切断点を含む。
使われ方：出力の終点を元の右側出現へ戻す。 -/
lemma one_mem_edgeOutputVertices_iff {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) (k : Fin n) :
    1 ∈ edgeOutputVertices u p k ↔ ∃ i : Fin l, p ≤ i ∧ u i = k := by
  simpa using edgeOutputVertices_mem_iff u p k 1

/-- 概要：二頂点の全体集合への一致は両頂点の所属で判定できる（BF §2.2.1）。
方針：二元の有限型の全要素を調べる。
規約：出力集合は空でもよい。
使われ方：辺の出力を左右の色の出現へ特徴付ける。 -/
lemma edgeOutputVertices_eq_univ_iff_mem {n l : ℕ} (u : Fin l → Fin n)
    (p : Fin l) (k : Fin n) : edgeOutputVertices u p k = Finset.univ ↔
      (0 : Fin 2) ∈ edgeOutputVertices u p k ∧ (1 : Fin 2) ∈ edgeOutputVertices u p k := by
  rw [Finset.eq_univ_iff_forall]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

/-- 概要：非零切断の辺の色は活動位置の色にちょうど一致する（BF §2.2.3）。
方針：左右の同色出現は切断点自身か区切りを与え、逆に区切りは切断点を跨ぐ。
規約：活動位置は区切りと切断点。
使われ方：テンソル境界の因子を元の語の削除位置で添字付ける。 -/
lemma edgeOutputVertices_eq_univ_iff_active {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : EdgeNondegenerate u p) (k : Fin n) :
    edgeOutputVertices u p k = Finset.univ ↔ ∃ i ∈ activePositions u p, u i = k := by
  rw [edgeOutputVertices_eq_univ_iff_mem, zero_mem_edgeOutputVertices_iff,
    one_mem_edgeOutputVertices_iff]
  constructor
  · rintro ⟨⟨i, hi, hui⟩, ⟨j, hj, huj⟩⟩
    refine ⟨i, ?_, hui⟩
    by_cases hip : i = p
    · exact Finset.mem_insert.mpr (Or.inl hip)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨j, lt_of_lt_of_le (lt_of_le_of_ne hi hip) hj, huj.trans hui.symm⟩⟩))
  · rintro ⟨i, hi, hui⟩
    rcases Finset.mem_insert.mp hi with hip | hi
    · subst i
      exact ⟨⟨p, le_rfl, hui⟩, ⟨p, le_rfl, hui⟩⟩
    · obtain ⟨j, hij, hji⟩ := (Finset.mem_filter.mp hi).2
      have hs := repeated_straddles h hij hji.symm
      exact ⟨⟨i, hs.1.le, hui⟩, ⟨j, hs.2.le, hji.trans hui⟩⟩

/-- 概要：基底語の出力が辺であることは活動位置の色に等しいことと同値（BF §2.2.3）。
方針：面の部分型の一致を頂点集合の一致へ移す。
規約：全 arity・全次数。
使われ方：実際のテンソル境界の辺だけの有限和を活動位置の和へ移す。 -/
lemma edgeOutput_eq_edge_iff {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) (k : Fin n) :
    edgeOutput u p k = edge ↔ ∃ i ∈ activePositions u.val p, u.val i = k := by
  rw [← edgeOutputVertices_eq_univ_iff_active h k]
  exact Subtype.ext_iff

end SerrePositivity.EInfinity.IntervalCuts
