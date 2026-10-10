module

public import SerrePositivity.Inputs.LengthAlgebra
public import SerrePositivity.Inputs.RegularLocalRing
public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import SerrePositivity.IntersectionMultiplicity.NormalizedTor

/-!
# 系2.6：長さ代数への有限長加群の係数拡大

定理2.5の入力と有限長加群の Tor に関する一般定理から導く。
`cor_2_6_tor` は証明済み（正則局所環の入力に依存）、`cor_2_6_pos` は未証明。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

/-- **Corollary 2.6** の 1・2（有限長の基底変更）。`r = rank_A D` とすると、有限長 `A` 加群 `V` で
`λ Tor_i^A(C_D, V) = 0 (i > 0)`、`λ Tor_0^A(C_D, V) = r · length_A V`（`Tor_0 = C_D ⊗_A V`）。
一般定理 `normalizedLength_tor_of_isWeaklyRegular`を `z = t` に適用する。 -/
theorem cor_2_6_tor (A D : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] [Module.Finite A D] {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (C : Type u) [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hC : LengthAlgebraProps A D t C lam)
    (V : Type u) [AddCommGroup V] [Module A V] (hV : Module.length A V ≠ ⊤) :
    (∀ i : ℕ, 0 < i → lam.len (TorAlg (algebraMap A C) i V) = 0) ∧
      lam.len (TorAlg (algebraMap A C) 0 V) =
        (Module.finrank A D : ℝ≥0∞) * ENat.toENNReal (Module.length A V) := by
  have hVfl : IsFiniteLength A V := Module.length_ne_top_iff.mp hV
  have hreg := isWeaklyRegular_of_span_eq_maximalIdeal A t ht hdim
  let lam' := lam.restrictToBase A D
  obtain ⟨h39a, h39b⟩ := hC.base_values_one hsop
  have := normalizedLength_tor_of_isWeaklyRegular (algebraMap A C) t ht hreg lam'
    (Module.finrank A D) h39a h39b V hVfl
  exact ⟨this.1, this.2.1⟩

/-- **Corollary 2.6** の 3：`λ(C_D/𝔡 C_D) > 0`。(2.5) と `D/H` の組成列による（未証明）。 -/
theorem cor_2_6_pos (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] {h : ℕ} (t : Fin h → A) (_hbase : IsRegularNormalizationBase A D t)
    (C : Type u) [CommRing C] [Algebra D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (_hC : LengthAlgebraProps A D t C lam) :
    0 < lam.len (C ⧸ (maximalIdeal D).map (algebraMap D C)) := by
  sorry

end SerrePositivity
