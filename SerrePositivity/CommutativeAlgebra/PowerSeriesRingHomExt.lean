module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesVariableRegular
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # 冪級数環からの環準同型の一意性

## 概要

有限個の変数の冪級数環 `K[[X]]` から環 `B` への二つの環準同型が、定数と変数の上で一致し、
変数の像がイデアル `J` に入り、`B` が `J` 進分離的なら、二つは等しい。

## 方針

全次数 `N` 未満の係数が消える冪級数は `(X)^N` に入る（`mem_span_X_pow_of_coeff`）。
変数ごとに `f = X_j g + h` と分けることを全変数について繰り返し、残りが定数項だけになることを使う。
`f` から全次数 `N` 未満の切り捨て（多項式）を引いた差は `(X)^N` に入り、
二つの準同型は多項式の上で一致するので、像の差は `J^N` に入る。分離性から等しい。

## 使われ方

解説の付録 A（「引用している結果」の対角線論法の段落）の工程（対角線写像と係数写像の合成の計算）。
対角線の評価 `Δ : R[[Y]] → R` と係数写像 `R → R[[Y]]` の合成が恒等写像であることに使う。
-/

@[expose] public section

universe u

open MvPowerSeries

namespace SerrePositivity

variable {K : Type u} [CommRing K] {σ : Type*}

/-- 有限個の変数の集合 `s` について、`f = Σ_{j ∈ s} X_j g_j + h` と分ける。`g_j` の係数は `f` の係数を
ずらしたもの、`h` は `s` の変数を含まない単項式の部分。 -/
theorem exists_sum_X_mul_add (N : ℕ) (f : MvPowerSeries σ K)
    (hf : ∀ α : σ →₀ ℕ, α.degree < N + 1 → coeff α f = 0) (s : Finset σ) :
    ∃ (g : σ → MvPowerSeries σ K) (h : MvPowerSeries σ K),
      f = ∑ j ∈ s, X j * g j + h ∧
      (∀ j ∈ s, ∀ β : σ →₀ ℕ, β.degree < N → coeff β (g j) = 0) ∧
      ∀ α : σ →₀ ℕ, coeff α h = if (∀ j ∈ s, α j = 0) then coeff α f else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ 0, f, by simp, by simp, by simp⟩
  | insert j s hj ih =>
    obtain ⟨g, h, hfgh, hg, hh⟩ := ih
    obtain ⟨g', h', hh', hcoeff, hg'⟩ := exists_X_mul_add_of_coeff h j
    refine ⟨Function.update g j g', h', ?_, ?_, ?_⟩
    · rw [Finset.sum_insert hj, Function.update_self, hfgh, hh']
      have : ∑ i ∈ s, X i * Function.update g j g' i = ∑ i ∈ s, X i * g i :=
        Finset.sum_congr rfl fun i hi ↦ by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
      rw [this]
      ring
    · intro i hi β hβ
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · rw [Function.update_self, hg', hh]
        split_ifs
        · apply hf
          rw [map_add, Finsupp.degree_single]
          omega
        · rfl
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi' hj)]
        exact hg i hi' β hβ
    · intro α
      rw [hcoeff, hh]
      by_cases hαj : α j = 0
      · simp only [hαj, ite_true, Finset.mem_insert, forall_eq_or_imp, true_and]
      · simp [hαj]

/-- **低次の係数が消える冪級数**：全次数 `N` 未満の係数が消える冪級数は `(X)^N` に入る。 -/
theorem mem_span_X_pow_of_coeff [Fintype σ] (N : ℕ) (f : MvPowerSeries σ K)
    (hf : ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) :
    f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ^ N := by
  classical
  induction N generalizing f with
  | zero => simp
  | succ N ih =>
    obtain ⟨g, h, hfgh, hg, hh⟩ := exists_sum_X_mul_add N f hf Finset.univ
    -- 残りは定数項だけで、それも消える
    have hh0 : h = 0 := by
      ext α
      rw [hh, map_zero]
      split_ifs with hα
      · apply hf
        have : α = 0 := Finsupp.ext fun i ↦ hα i (Finset.mem_univ i)
        simp [this]
      · rfl
    rw [hfgh, hh0, add_zero, pow_succ']
    refine Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) ?_
    exact ih (g j) (hg j (Finset.mem_univ j))

/-- **冪級数環からの環準同型の一意性**：定数と変数の上で一致し、変数の像が `J` に入り、
`B` が `J` 進分離的なら、二つの環準同型は等しい。全次数の切り捨てとの差が `(X)^N` に入ることによる。 -/
theorem MvPowerSeries.ringHom_ext_of_isHausdorff [Finite σ] {B : Type*} [CommRing B]
    (J : Ideal B) [IsHausdorff J B] {φ ψ : MvPowerSeries σ K →+* B}
    (hC : φ.comp C = ψ.comp C) (hX : ∀ i, φ (X i) = ψ (X i)) (hJ : ∀ i, φ (X i) ∈ J) :
    φ = ψ := by
  classical
  let := Fintype.ofFinite σ
  -- 多項式の上では一致する
  have hpoly : φ.comp (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := K)) =
      ψ.comp MvPolynomial.coeToMvPowerSeries.ringHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have := RingHom.congr_fun hC a
      simpa using this
    · intro i
      simpa using hX i
  -- 変数のイデアルの冪の像は `J` の冪に入る
  have hmap : ∀ N, ∀ r ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ^ N,
      φ r ∈ J ^ N ∧ ψ r ∈ J ^ N := by
    intro N r hr
    have hle : ∀ χ : MvPowerSeries σ K →+* B, (∀ i, χ (X i) ∈ J) →
        (Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ^ N).map χ ≤ J ^ N := by
      intro χ hχ
      rw [Ideal.map_pow]
      apply Ideal.pow_right_mono
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hχ i
    exact ⟨hle φ hJ (Ideal.mem_map_of_mem _ hr),
      hle ψ (fun i ↦ hX i ▸ hJ i) (Ideal.mem_map_of_mem _ hr)⟩
  ext f
  rw [← sub_eq_zero]
  apply IsHausdorff.haus (inferInstance : IsHausdorff J B)
  intro N
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  set p : MvPolynomial σ K := MvPowerSeries.truncTotal N f
  have hr : f - (p : MvPowerSeries σ K) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) ^ N := by
    apply mem_span_X_pow_of_coeff
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hα, sub_self]
  have hp : φ (p : MvPowerSeries σ K) = ψ p := RingHom.congr_fun hpoly p
  have hsplit : φ f - ψ f = φ (f - p) - ψ (f - p) := by
    rw [map_sub, map_sub, hp]
    ring
  rw [hsplit]
  exact sub_mem (hmap N _ hr).1 (hmap N _ hr).2

end SerrePositivity
