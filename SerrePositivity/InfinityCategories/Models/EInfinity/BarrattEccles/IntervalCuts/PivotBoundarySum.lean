module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutConvexity
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapTensors
public import Mathlib.Algebra.BigOperators.Intervals

/-!
模型。文献の定義との比較は後で
# 切断点色の因子境界の望遠和

概要：Berger–Fresse §2.2.7 の切断点色の実際の全境界和は非零切断区間の二端点だけになる。
方針：非零切断の凸性と共通係数を使い、隙間テンソルの隣接差を望遠和にする。
規約：全ての値を実際の反復テンソルの次数 −d へ移して加える。
使われ方：切断点障害の削除項と次数零の入力辺境界の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：切断点色の実際の符号付き因子境界を共通次数へ移した値（BF §2.2.7）。
方針：非零切断なら実際の因子境界を移し、退化切断なら零とする。
規約：出力次数は −d。
使われ方：全切断の因子境界和の切断点色部分。 -/
def pivotBoundaryValue {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d)) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-(d : ℤ)) :=
  if h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p then
    eqToHom (congrArg (fun r : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X r)
        (by have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u p h
            omega : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) : ℤ) + 1 = -(d : ℤ)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (u.val p))
  else 0

/-- 概要：非零切断の因子境界値は共通係数付き隙間差（BF §2.2.7）。
方針：定義の判定を解いて切断点色の端点公式を使う。
規約：係数は全区切りだけに依存する。
使われ方：境界値の有限和を望遠和へ変える。 -/
lemma pivotBoundaryValue_eq {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (p : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p =
      ((-1 : ℤ) ^ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)).card *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val))) •
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u p.castSucc - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u p.succ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue, dite_eq_left h]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundary_gap_difference A u p h

/-- 概要：非零切断二点間の切断点色の実際の因子境界和は両隙間の差（BF §2.2.7）。
方針：中間切断の非零性で全項を隙間差へ移し、有限順序区間の望遠和を取る。
規約：区間は両端の切断点を含む。
使われ方：全非零切断区間の境界を二端点へ集約する。 -/
lemma pivotBoundaryValue_sum_Icc {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (a b : Fin (n + d))
    (hab : a ≤ b) (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val a) (hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val b) :
    ∑ p ∈ Finset.Icc a b, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p =
      ((-1 : ℤ) ^ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)).card *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val))) •
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u a.castSucc - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u b.succ) := by
  calc
    _ = ∑ p ∈ Finset.Icc a b,
        ((-1 : ℤ) ^ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)).card *
          (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val))) •
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u p.castSucc - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u p.succ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue_eq A u p
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_between ha hb (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hp).2)
    _ = _ := by
      rw [← Finset.smul_sum]
      congr 1
      simpa only [neg_sub_neg] using Fin.sum_Icc_sub hab (fun q => -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u q)

/-- 概要：非零切断の最小・最大が指定されれば全因子境界和は二つの隙間値（BF §2.2.7）。
方針：非零集合を凸性で順序区間へ同定し、外の退化項を零として除く。
規約：両端の非零性と全非零点の範囲だけを要求する。
使われ方：選んだ最小・最大切断から全有限和の両端表示を得る。 -/
lemma pivotBoundaryValue_sum_of_endpoints {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (a b : Fin (n + d)) (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val a) (hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val b)
    (hends : ∀ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p → a ≤ p ∧ p ≤ b) :
    ∑ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p =
      ((-1 : ℤ) ^ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)).card *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val))) •
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u a.castSucc - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u b.succ) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue_sum_Icc A u a b (hends b hb).1 ha hb]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  have hdeg : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p := fun h => hp (Finset.mem_Icc.mpr (hends p h))
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue, dite_eq_right hdeg]

/-- 概要：切断点色の全境界和は非零区間の両隙間差、空なら零（BF §2.2.7）。
方針：非零切断の有限集合の最小・最大を選び、区間の望遠和公式を使う。
規約：端点の存在や切断の非零性を外部仮定にしない。
使われ方：切断点障害の削除和との無条件な全有限和比較。 -/
lemma pivotBoundaryValue_sum {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    let s := Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val)
    ∑ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p =
      if hs : s.Nonempty then
        ((-1 : ℤ) ^ (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val)).card *
          (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val))) •
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u (s.min' hs).castSucc - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u (s.max' hs).succ)
      else 0 := by
  intro s
  by_cases hs : s.Nonempty
  · rw [dite_eq_left hs]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue_sum_of_endpoints A u (s.min' hs) (s.max' hs)
      (Finset.mem_filter.mp (s.min'_mem hs)).2 (Finset.mem_filter.mp (s.max'_mem hs)).2
    intro p hp
    have hp' : p ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
    exact ⟨s.min'_le p hp', s.le_max' p hp'⟩
  · rw [dite_eq_right hs]
    apply Finset.sum_eq_zero
    intro p _
    have hp : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p := fun hp => hs
      ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue, dite_eq_right hp]

/-- 概要：次数零の全切断点色境界和は入力辺の終点テンソルと始点テンソルの差（BF §2.2.7）。
方針：次数零の語は色の置換なので全切断が非零、区切り集合は空となる。
規約：arity 零では二つの空テンソルの差として零となる。
使われ方：χ の微分保存の次数零における入力辺境界項。 -/
lemma pivotBoundaryValue_sum_zeroDegree {n : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0) :
    ∑ p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue A u p =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n 0 (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree n 1) -
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n 0 (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree n 0) := by
  cases n with
  | zero =>
    have he : (fun _ : Fin 0 => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 1) = (fun _ : Fin 0 => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex 0) :=
      funext (fun i => Fin.elim0 i)
    simp only [he, sub_self]
    exact Finset.sum_eq_zero (fun p _ => Fin.elim0 p)
  | succ n =>
    have hinj : Function.Injective u.val := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexNondegenerate_iff u).mpr rfl
    have hc : Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨j, hij, hu⟩ := (Finset.mem_filter.mp hi).2
      exact (ne_of_lt hij) (hinj hu.symm)
    have hall (p : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p := by
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff_straddles u.val p).mpr
      intro i j hij hu
      exact False.elim ((ne_of_lt hij) (hinj hu))
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotBoundaryValue_sum_of_endpoints A u 0 (Fin.last n) (hall 0)
      (hall (Fin.last n)) (fun p _ => ⟨Fin.zero_le p, Fin.le_last p⟩)
    simpa only [hc, Finset.card_empty, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount, Finset.sum_empty,
      pow_zero, mul_one, one_smul, Fin.castSucc_zero, Fin.succ_last,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor_first_zeroDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor_last_zeroDegree] using! h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
