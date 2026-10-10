module

public import SerrePositivity.Paper.Section5.ParameterQuotient
public import SerrePositivity.Paper.Section5.ApproximationHomology

/-! # パラメータ商の有限近似が満たす Betti 数の増大条件

Lemma 5.4 の剰余体 Tor 極限に Lemma 5.3 の有限性・消滅を適用する。
切り詰めより上の `o(s)` を独立に仮定する必要はない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section5

open CategoryTheory Filter Topology IsLocalRing ParamQuot Asymptotic Asymptotics
open scoped ENNReal

variable {R C : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing C]

/-- `dim R = l + h` のとき、剰余体 Tor の近似から、`l` 次までの `O(s)` と
`l` 次より上の全次数の `o(s)` が従う。商 `B = R/(x)` の正則性は仮定しない。 -/
theorem betti_growth_of_parameter_approximation
    (φ : R →+* C) {h : ℕ} (x : Fin h → R) [IsLocalRing (B x)]
    {J : Ideal C} (lam : NormalizedLength C J) (l : ℕ) (hd : ringKrullDim R = (l + h : ℕ))
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (hfg : J.FG) {b : ℕ} (hJ : J ^ b ≤ IC φ x)
    (hJrad : J ≤ (Ideal.span (Set.range (φ ∘ x))).radical)
    (hzero : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      lam.len (koszulHomologySelf (fun j ↦ φ (x j ^ v)) q) = 0)
    (hUfin : lam.len (U φ x) ≠ ⊤)
    (M : ℕ → FGModuleCat.{u} (B x)) {s : ℕ → ℕ} (hs : ∀ n, 0 < s n)
    (hlim : ∀ i, Tendsto (fun n ↦
      (Module.length (B x) (TorModule (B x) i (M n) (B x ⧸ maximalIdeal (B x))) : ℝ≥0∞) /
        (s n : ℝ≥0∞)) atTop
          (𝓝 (lam.len (TorAlg φ i (B x ⧸ maximalIdeal (B x)))))) :
    (∀ i ≤ l,
      (fun n ↦ ((Module.length (B x)
        (TorModule (B x) i (M n) (B x ⧸ maximalIdeal (B x)))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ))) ∧
    (∀ i, l < i →
      (fun n ↦ ((Module.length (B x)
        (TorModule (B x) i (M n) (B x ⧸ maximalIdeal (B x)))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) := by
  have htor (i : ℕ) := lemma_5_3 φ x lam hd hreg hfg hJ hJrad hzero hUfin
    (B x ⧸ maximalIdeal (B x)) i
  exact betti_growth_of_approximation_limits M l hs
    (fun i ↦ lam.len (TorAlg φ i (B x ⧸ maximalIdeal (B x))))
    (fun i ↦ (htor i).2.1) (fun i hi ↦ (htor i).2.2 (by omega)) hlim

end SerrePositivity.Section5
