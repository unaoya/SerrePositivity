module

public import SerrePositivity.CommutativeAlgebra.FrobeniusHypersurfaceGrowth
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import Mathlib.Algebra.CharP.Quotient

/-! # `A/(p, g)` の Frobenius 長さの低次元評価

## 概要

`p` を先頭に持つ極小な極大イデアル生成列から、`A/p` の正則局所性・次元・標数・整域性を確かめ、`p ∤ g` で `g ∈ m` のとき `g` の像が `A/p` の非零因子であることを示す。これにより、超曲面 `A/(p, g)` の Frobenius 冪の商の長さに、指数 `dim A - 2` で一般の増大評価（CommutativeAlgebra/FrobeniusHypersurfaceGrowth）を当て、正規化した長さが零へ収束することを得る。

## 方針

正則局所環の商の正則性と次元公式を使って一般評価の仮定を確かめる。

## 規約

有限段の Witt 冪級数の Frobenius 比較はここに含めない（CommutativeAlgebra/RootTower/StageModPLength）。旧 `CLMST/ModPHypersurfaceGrowth`。

## 使われ方

`RootTower/StageModPLength`、CLMST の `CyclicLengthBound`（Prop 4.0.10）。
-/

@[expose] public noncomputable section

universe u

section ModPHypersurfaceGrowthPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open IsLocalRing
open scoped ENNReal

/-- 最小生成列の先頭がpなら、A/pは正則局所環で次元が一つ小さい。 -/
theorem modP_regular_and_dim_of_parameters
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) :
    IsRegularLocalRing (A ⧸ Ideal.span {(p : A)}) ∧
      ringKrullDim (A ⧸ Ideal.span {(p : A)}) = r + 1 := by
  have hQ := isRegularLocalRing_quotient_head_and_dim t ht hdim
  rw [htp] at hQ
  simpa only [Nat.cast_add, Nat.cast_one] using hQ

/-- pが極大イデアルに含まれることから、A/pの標数pを供給する。 -/
theorem modP_charP_of_parameters
    (A : Type u) [CommRing A] [IsLocalRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A)) :
    CharP (A ⧸ Ideal.span {(p : A)}) p := by
  have hp : (p : A) ∈ maximalIdeal A := by
    rw [← htp, ← ht]
    exact Ideal.subset_span (Set.mem_range_self 0)
  exact CharP.quotient A p (by simpa only [mem_maximalIdeal] using hp)

/-- 最小生成列の先頭がpであるとき、A/pは整域。
正則生成列の一般論から供給し、型クラスを大域的には登録しない。 -/
theorem modP_isDomain_of_parameters
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) : IsDomain (A ⧸ Ideal.span {(p : A)}) := by
  let Q := A ⧸ Ideal.span {(p : A)}
  let : IsRegularLocalRing Q := (modP_regular_and_dim_of_parameters A t p ht htp hdim).1
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators Q
  exact isDomain_of_regular_generators rs hreg hgen

/-- pがgを割らなければ、gのA/pでの像は非零因子。
A/pの整域性は正則生成列の一般論から供給する。 -/
theorem modP_image_mem_nonZeroDivisors_of_not_dvd
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (g : A) (hpg : ¬ (p : A) ∣ g) :
    Ideal.Quotient.mk (Ideal.span {(p : A)}) g ∈
      nonZeroDivisors (A ⧸ Ideal.span {(p : A)}) := by
  let Q := A ⧸ Ideal.span {(p : A)}
  let : IsDomain Q := modP_isDomain_of_parameters A t p ht htp hdim
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro hg
  exact hpg (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hg))

/-- pと非零のmod p像を持つ非単元gで割ると、次元が二つ下がる。 -/
theorem modP_hypersurface_dim
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (g : A)
    (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g) :
    ringKrullDim ((A ⧸ Ideal.span {(p : A)}) ⧸
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) g}) = r := by
  let Q := A ⧸ Ideal.span {(p : A)}
  have hQ := modP_regular_and_dim_of_parameters A t p ht htp hdim
  let : IsRegularLocalRing Q := hQ.1
  let q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hgQ : q g ∈ maximalIdeal Q := by
    have hh := Ideal.mem_map_of_mem q hgm
    rwa [map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective] at hh
  exact ringKrullDim_quotient_eq_of_nonZeroDivisor Q (q g)
    (modP_image_mem_nonZeroDivisors_of_not_dvd A t p ht htp hdim g hpg) hgQ hQ.2

/-- A/(p,g)側のFrobenius商の通常長さは、指数r=dim(A)-2の一様な有限上界を持つ。
成長の次元低下と、非零因子であることの確認をこの入口で供給する。 -/
theorem exists_modP_hypersurface_length_bound
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (g : A)
    (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g) :
    let Q := A ⧸ Ideal.span {(p : A)}
    letI : IsRegularLocalRing Q := (modP_regular_and_dim_of_parameters A t p ht htp hdim).1
    letI : CharP Q p := modP_charP_of_parameters A t p ht htp
    ∃ c : ℕ, ∀ n : ℕ,
      Module.length Q (Q ⧸ ((maximalIdeal Q).map (iterateFrobenius Q p n) ⊔
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) g})) ≤
          ((p ^ n : ℕ) : ℕ∞) ^ r * (c : ℕ∞) := by
  let Q := A ⧸ Ideal.span {(p : A)}
  have hQ := modP_regular_and_dim_of_parameters A t p ht htp hdim
  let : IsRegularLocalRing Q := hQ.1
  let : CharP Q p := modP_charP_of_parameters A t p ht htp
  let q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hgQ : q g ∈ maximalIdeal Q := by
    have hh := Ideal.mem_map_of_mem q hgm
    rwa [map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective] at hh
  exact exists_frobenius_hypersurface_length_bound Q p (q g)
    (modP_image_mem_nonZeroDivisors_of_not_dvd A t p ht htp hdim g hpg) hgQ hQ.2

/-- 今回のA/(p,g)側の長さをp^(n(dim(A)-1))で割った値は零へ収束する。
有限段との比較前に、低次元の数値評価を独立に確定する。 -/
theorem tendsto_modP_hypersurface_normalized_length_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (g : A)
    (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g) :
    let Q := A ⧸ Ideal.span {(p : A)}
    letI : IsRegularLocalRing Q := (modP_regular_and_dim_of_parameters A t p ht htp hdim).1
    letI : CharP Q p := modP_charP_of_parameters A t p ht htp
    Filter.Tendsto (fun n : ℕ ↦
      (Module.length Q (Q ⧸ ((maximalIdeal Q).map (iterateFrobenius Q p n) ⊔
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) g})) : ℝ≥0∞) /
          ((p : ℝ≥0∞) ^ n) ^ (r + 1)) Filter.atTop (nhds 0) := by
  let Q := A ⧸ Ideal.span {(p : A)}
  have hQ := modP_regular_and_dim_of_parameters A t p ht htp hdim
  let : IsRegularLocalRing Q := hQ.1
  let : CharP Q p := modP_charP_of_parameters A t p ht htp
  let q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hgQ : q g ∈ maximalIdeal Q := by
    have hh := Ideal.mem_map_of_mem q hgm
    rwa [map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective] at hh
  exact tendsto_frobenius_hypersurface_normalized_length_zero Q p (Fact.out : p.Prime).one_lt
    (q g) (modP_image_mem_nonZeroDivisors_of_not_dvd A t p ht htp hdim g hpg) hgQ hQ.2

end SerrePositivity

end ModPHypersurfaceGrowthPart
