module

public import SerrePositivity.PerfectComplex.KoszulLengthBounds
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# 長さの上界から漸近評価への接続

## 概要

固定された有限個の有限な重みと、自然数値の大きさの列による上界を、
実数値の `O`・`o` 評価へ移す。§4 では重みが環の Koszul ホモロジーの長さ、
大きさが係数複体の各項の基底の個数となる。

## 方針と規約

まず `ℝ≥0∞` の上界から有限性を確認して `toReal` をとり、Mathlib の
有限和と定数倍の漸近評価を使う。漸近評価は通常の `atTop` に関するもので、
超フィルター極限とは区別する。共通の次数範囲と固定された重みを引数にすることで、
列の添字に依存しない定数による上界を得る。
-/

@[expose] public section

universe u

open CategoryTheory Limits Filter Asymptotics
open scoped ENNReal BigOperators

namespace SerrePositivity

/-- 有限な重みの自然数倍の有限和は有限。長さの実数化の前提に用いる。 -/
lemma ennreal_sum_nsmul_ne_top {ι : Type*} (I : Finset ι) (c : ι → ℝ≥0∞)
    (hc : ∀ i ∈ I, c i ≠ ⊤) (r : ι → ℕ) : (∑ i ∈ I, r i • c i) ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro i hi
  simpa only [nsmul_eq_mul] using ENNReal.mul_ne_top (by simp : (r i : ℝ≥0∞) ≠ ⊤) (hc i hi)

/-- 有限な重みの自然数倍の和で長さが抑えられれば、実数化後も同じ上界をもつ。
右辺の有限性を先に確保し、`toReal` の単調性と有限和との可換性を使う。 -/
lemma ennreal_toReal_le_sum_nsmul {ι : Type*} (I : Finset ι) (c : ι → ℝ≥0∞)
    (hc : ∀ i ∈ I, c i ≠ ⊤) (r : ι → ℕ) {v : ℝ≥0∞}
    (hv : v ≤ ∑ i ∈ I, r i • c i) :
    v.toReal ≤ ∑ i ∈ I, (r i : ℝ) * (c i).toReal := by
  have hf : ∀ i ∈ I, r i • c i ≠ ⊤ := ENNReal.sum_ne_top.mp (ennreal_sum_nsmul_ne_top I c hc r)
  have h := ENNReal.toReal_mono (ennreal_sum_nsmul_ne_top I c hc r) hv
  rw [ENNReal.toReal_sum hf] at h
  simpa only [nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast] using h

/-- 固定された有限な重みと `O(s)` の自然数列の和に抑えられる長さも `O(s)`。
この補題では列の添字は任意のフィルターでよく、超極限の存在は使わない。 -/
lemma ennreal_isBigO_of_le_sum_nsmul {α ι : Type*} (l : Filter α)
    (I : Finset ι) (c : ι → ℝ≥0∞) (hc : ∀ i ∈ I, c i ≠ ⊤)
    (r : α → ι → ℕ) (v : α → ℝ≥0∞) (s : α → ℝ)
    (hv : ∀ k, v k ≤ ∑ i ∈ I, r k i • c i)
    (hr : ∀ i ∈ I, (fun k ↦ (r k i : ℝ)) =O[l] s) :
    (fun k ↦ (v k).toReal) =O[l] s := by
  have hdom : (fun k ↦ (v k).toReal) =O[l]
      (fun k ↦ ∑ i ∈ I, (r k i : ℝ) * (c i).toReal) :=
    IsBigO.of_norm_le (fun k ↦ by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ennreal_toReal_le_sum_nsmul I c hc (r k) (hv k))
  apply hdom.trans
  apply IsBigO.fun_sum
  intro i hi
  simpa only [mul_comm] using (hr i hi).const_mul_left (c i).toReal

/-- 固定された有限な重みと `o(s)` の自然数列の和に抑えられる長さも `o(s)`。
実数化した上界への `O` と、その上界の `o` を合成する。 -/
lemma ennreal_isLittleO_of_le_sum_nsmul {α ι : Type*} (l : Filter α)
    (I : Finset ι) (c : ι → ℝ≥0∞) (hc : ∀ i ∈ I, c i ≠ ⊤)
    (r : α → ι → ℕ) (v : α → ℝ≥0∞) (s : α → ℝ)
    (hv : ∀ k, v k ≤ ∑ i ∈ I, r k i • c i)
    (hr : ∀ i ∈ I, (fun k ↦ (r k i : ℝ)) =o[l] s) :
    (fun k ↦ (v k).toReal) =o[l] s := by
  have hdom : (fun k ↦ (v k).toReal) =O[l]
      (fun k ↦ ∑ i ∈ I, (r k i : ℝ) * (c i).toReal) :=
    IsBigO.of_norm_le (fun k ↦ by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ennreal_toReal_le_sum_nsmul I c hc (r k) (hv k))
  apply hdom.trans_isLittleO
  apply IsLittleO.fun_sum
  intro i hi
  simpa only [mul_comm] using (hr i hi).const_mul_left (c i).toReal

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- 共通の次数範囲をもつ複体列で各項の基底の個数が `O(s)` なら、固定した
Koszul 複体を施した各ホモロジーの長さも `O(s)`。定数は列の添字に依存しない。 -/
lemma lambdaHomology_koszulComplexOn_isBigO (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ i, lam.len ((koszulComplex x).homology i) ≠ ⊤)
    (a : ℤ) (w : ℕ) (r : ℕ → ℤ → ℕ) (P : ℕ → CochainComplex (ModuleCat.{u} C) ℤ)
    (hbound : ∀ k i, (i < a ∨ a + w ≤ i) → IsZero ((P k).X i))
    (hterm : ∀ k i, a ≤ i → i < a + w →
      Nonempty ((P k).X i ≅ ModuleCat.of C (Fin (r k i) → C)))
    (s : ℕ → ℝ) (hr : ∀ i, a ≤ i → i < a + w → (fun k ↦ (r k i : ℝ)) =O[atTop] s)
    (q : ℤ) : (fun k ↦ (lam.len ((koszulComplexOn x (P k)).homology q)).toReal) =O[atTop] s := by
  apply ennreal_isBigO_of_le_sum_nsmul atTop (Finset.range w)
    (fun j ↦ lam.len ((koszulComplex x).homology (q - (a + j)))) (fun _ _ ↦ hfin _)
    (fun k j ↦ r k (a + j))
  · intro k
    exact lambdaHomology_koszulComplexOn_le_sum lam hfg x hJ a w (r k) (P k)
      (hbound k) (hterm k) q
  · intro j hj
    exact hr (a + j) (by omega) (by have := Finset.mem_range.mp hj; omega)

/-- 共通の次数範囲をもつ複体列で各項の基底の個数が `o(s)` なら、固定した
Koszul 複体を施した各ホモロジーの長さも `o(s)`。ランクで小さい対象を消すための評価。 -/
lemma lambdaHomology_koszulComplexOn_isLittleO (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ i, lam.len ((koszulComplex x).homology i) ≠ ⊤)
    (a : ℤ) (w : ℕ) (r : ℕ → ℤ → ℕ) (P : ℕ → CochainComplex (ModuleCat.{u} C) ℤ)
    (hbound : ∀ k i, (i < a ∨ a + w ≤ i) → IsZero ((P k).X i))
    (hterm : ∀ k i, a ≤ i → i < a + w →
      Nonempty ((P k).X i ≅ ModuleCat.of C (Fin (r k i) → C)))
    (s : ℕ → ℝ) (hr : ∀ i, a ≤ i → i < a + w → (fun k ↦ (r k i : ℝ)) =o[atTop] s)
    (q : ℤ) : (fun k ↦ (lam.len ((koszulComplexOn x (P k)).homology q)).toReal) =o[atTop] s := by
  apply ennreal_isLittleO_of_le_sum_nsmul atTop (Finset.range w)
    (fun j ↦ lam.len ((koszulComplex x).homology (q - (a + j)))) (fun _ _ ↦ hfin _)
    (fun k j ↦ r k (a + j))
  · intro k
    exact lambdaHomology_koszulComplexOn_le_sum lam hfg x hJ a w (r k) (P k)
      (hbound k) (hterm k) q
  · intro j hj
    exact hr (a + j) (by omega) (by have := Finset.mem_range.mp hj; omega)

/-- 各パラメータの零ホモトピーをもつ複体列では、元のホモロジーの長さも
基底の個数と同じ `O(s)` 評価をもつ。直和因子への上界の引き戻しを列に適用する。 -/
lemma lambdaHomology_isBigO_of_nullHomotopies (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ i, lam.len ((koszulComplex x).homology i) ≠ ⊤)
    (a : ℤ) (w : ℕ) (r : ℕ → ℤ → ℕ) (P : ℕ → CochainComplex (ModuleCat.{u} C) ℤ)
    (hbound : ∀ k i, (i < a ∨ a + w ≤ i) → IsZero ((P k).X i))
    (hterm : ∀ k i, a ≤ i → i < a + w →
      Nonempty ((P k).X i ≅ ModuleCat.of C (Fin (r k i) → C)))
    (hnull : ∀ k j, Nonempty (Homotopy (smulId (x j) (P k)) 0))
    (s : ℕ → ℝ) (hr : ∀ i, a ≤ i → i < a + w → (fun k ↦ (r k i : ℝ)) =O[atTop] s)
    (q : ℤ) : (fun k ↦ (lam.len ((P k).homology q)).toReal) =O[atTop] s := by
  apply ennreal_isBigO_of_le_sum_nsmul atTop (Finset.range w)
    (fun j ↦ lam.len ((koszulComplex x).homology (q - (a + j)))) (fun _ _ ↦ hfin _)
    (fun k j ↦ r k (a + j))
  · intro k
    exact lambdaHomology_le_sum_of_nullHomotopies lam hfg x hJ a w (r k) (P k)
      (hbound k) (hterm k) (hnull k) q
  · intro j hj
    exact hr (a + j) (by omega) (by have := Finset.mem_range.mp hj; omega)

/-- 各パラメータの零ホモトピーをもち、基底の個数が `o(s)` の複体列では、
元のホモロジーの長さも `o(s)`。通常の漸近的小ささを保持する。 -/
lemma lambdaHomology_isLittleO_of_nullHomotopies (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ i, lam.len ((koszulComplex x).homology i) ≠ ⊤)
    (a : ℤ) (w : ℕ) (r : ℕ → ℤ → ℕ) (P : ℕ → CochainComplex (ModuleCat.{u} C) ℤ)
    (hbound : ∀ k i, (i < a ∨ a + w ≤ i) → IsZero ((P k).X i))
    (hterm : ∀ k i, a ≤ i → i < a + w →
      Nonempty ((P k).X i ≅ ModuleCat.of C (Fin (r k i) → C)))
    (hnull : ∀ k j, Nonempty (Homotopy (smulId (x j) (P k)) 0))
    (s : ℕ → ℝ) (hr : ∀ i, a ≤ i → i < a + w → (fun k ↦ (r k i : ℝ)) =o[atTop] s)
    (q : ℤ) : (fun k ↦ (lam.len ((P k).homology q)).toReal) =o[atTop] s := by
  apply ennreal_isLittleO_of_le_sum_nsmul atTop (Finset.range w)
    (fun j ↦ lam.len ((koszulComplex x).homology (q - (a + j)))) (fun _ _ ↦ hfin _)
    (fun k j ↦ r k (a + j))
  · intro k
    exact lambdaHomology_le_sum_of_nullHomotopies lam hfg x hJ a w (r k) (P k)
      (hbound k) (hterm k) (hnull k) q
  · intro j hj
    exact hr (a + j) (by omega) (by have := Finset.mem_range.mp hj; omega)

end SerrePositivity
