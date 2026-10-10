module

public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.PerfectComplex.OrdinaryEuler
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! # 通常の長さによる Koszul 有限性 -/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal

/-- パラメータ商が Artin 環なら、各冪の Koszul ホモロジーの通常の長さは有限。 -/
lemma ordinary_koszul_pow_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) [IsArtinianRing (R ⧸ Ideal.span (Set.range z))]
    (v : ℕ) (i : ℤ) :
    (NormalizedLength.ordinary R).len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤ := by
  have : IsArtinianRing (R ⧸ Ideal.span (Set.range (fun j ↦ z j ^ v))) :=
    isArtinianRing_quotient_of_le_radical (Ideal.span (Set.range z)) _
      (le_radical_span_pow z Ideal.le_radical v)
  exact ENat.toENNReal_ne_top.mpr (Module.length_ne_top_iff.mpr
    (homology_finiteLength_of_isPerfectSupported
      (isPerfectSupported_koszulComplex (fun j ↦ z j ^ v)) i))

/-- Noether 局所環でパラメータの根基が極大イデアルを含めば、通常 Koszul 有限性を満たす。 -/
lemma ordinary_koszul_finite_of_maximal_le_radical
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R)
    (hz : IsLocalRing.maximalIdeal R ≤ (Ideal.span (Set.range z)).radical) :
    LengthAlgebra.KoszulFinite (NormalizedLength.ordinary R) z := by
  have : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R) :=
    inferInstanceAs (IsArtinianRing (IsLocalRing.ResidueField R))
  have : IsArtinianRing (R ⧸ Ideal.span (Set.range z)) :=
    isArtinianRing_quotient_of_le_radical (IsLocalRing.maximalIdeal R) _ hz
  exact fun v _ q ↦ ordinary_koszul_pow_finite z v q

end SerrePositivity
