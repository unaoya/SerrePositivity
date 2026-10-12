module

public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import SerrePositivity.PerfectComplex.NormalizedLength
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal

/-!
# 長さ代数の (2.4)、(2.6) を基底のパラメータで書き直す

## 概要

論文 Theorem 2.5 の長さ代数 `(C_D, λ_D)` の性質 (2.4)（正次数の Koszul ホモロジーの `λ_D` は `0`）と
(2.6)（`λ_D(C_D/(t^v)C_D) = v^h rank_A D`）を、基底 `A` のパラメータ系 `t` の冪について、`A → C` の
像で書き直す補題 `lengthAlgebra_base_values`、`lengthAlgebra_base_values_one`。Corollary 2.6
（`Paper/Corollary2_6.lean`）と Lemma 3.5 への適用で、(3.9) の形の仮定にするために使う。

Theorem 2.5 は `Paper/Section2/Theorem2_5.lean` の `Section2.theorem_2_5` にある。
その導出には証明が付いているが、標数別の構成
（`LengthAlgebraConstruction.lean`）の引用入力に依存する。一般的な重複度公式は証明済み。塔 `Λ` と `λ_∞` の定義は `Paper/Section2/Tower.lean`、
`TowerLength.lean`、Hilbert–Samuel 重複度は `CommutativeAlgebra/HilbertSamuel.lean`。
以前ここにあった `Inputs.exists_lengthAlgebra` は、塔の作用との両立を欠き、重複度を極限の式で
書いていたので、2026-10-10 に `theorem_2_5` に置き換えて削除した。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

section preparation

variable {A D C : Type u} [CommRing A] [CommRing D] [IsLocalRing D]
  [Algebra A D] [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
  {h : ℕ} {t : Fin h → A}

/-- (2.4) と (2.6) を、基底 `A` のパラメータ系 `t` の冪 `t^v` について、`A → C` の像で書き直したもの：
`λ(H_i(t^v; C)) = 0 (i > 0)` と `λ(C/(t^v)C) = v^h · rank_A D`。`t` の `D` での像がパラメータ系で
あること（`hsop`）を使い、`algebraMap D C ∘ algebraMap A D = algebraMap A C` で書き換えるだけ。
Corollary 2.6 と Lemma 3.5 で、`NormalizedTor.lean` の仮定 (3.9) の形にするために使う。 -/
theorem lengthAlgebra_base_values
    {lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))}
    (hzero : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0)
    (hbase : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (v : ℕ) (hv : 0 < v) :
    (∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (t j ^ v)) i) = 0) ∧
    lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (t j ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞) := by
  have heq : (fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ v)) =
      (fun j ↦ algebraMap A C (t j ^ v)) := by
    funext j
    simp [IsScalarTower.algebraMap_apply A D C]
  constructor
  · intro i hi
    have hz := hzero (algebraMap A D ∘ t) hsop v hv i hi
    rw [heq] at hz
    exact hz
  · have hq := hbase v hv
    change lam.len (C ⧸ Ideal.span
      (Set.range fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ v))) = _ at hq
    rw [heq] at hq
    exact hq

/-- `base_values` の `v = 1` の場合：`λ(H_i(t; C)) = 0 (i > 0)` と `λ(C/tC) = rank_A D`。 -/
theorem lengthAlgebra_base_values_one
    {lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))}
    (hzero : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0)
    (hbase : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) :
    (∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (algebraMap A C ∘ t) i) = 0) ∧
    lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ t))) =
      Module.finrank A D := by
  have ht : (fun j ↦ algebraMap A C (t j ^ 1)) = algebraMap A C ∘ t := by
    funext j
    simp
  have hv := lengthAlgebra_base_values hzero hbase hsop 1 one_pos
  rw [ht] at hv
  simpa only [one_pow, one_mul] using hv

end preparation


end SerrePositivity
