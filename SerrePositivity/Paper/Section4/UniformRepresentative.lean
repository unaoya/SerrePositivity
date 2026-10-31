module

public import SerrePositivity.Asymptotic.SupportedRankTStructure
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.KoszulResolution

/-!
# §4 の A 側の一様自由代表

極大イデアルを生成する列の Koszul 完全性から、
支持つきランク商の冪等完備性を得る。
任意の Koszul Euler 数による基底公式を、論文の支持圏へ移す際に使う。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section4

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents IsLocalRing
open SerrePositivity.Asymptotic

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)
  (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
  {s : ℕ → ℕ}

include hz hKoszul in
/-- A 側の支持つきランク商は、Koszul 完全性の下で冪等完備。 -/
theorem supportedRank_isIdempotentComplete_of_koszul :
    IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z) := by
  have hres : IsResolutionOf (koszulComplex z) (ModuleCat.of A (A ⧸ maximalIdeal A)) := by
    have h := isResolutionOf_koszul z hKoszul
    rw [hz] at h
    exact h
  have := isArtinianRing_quotient_span_of_eq hz
  exact supportedRank_isIdempotentComplete z (koszulComplex z) hres
    (fun i ↦ (koszulComplex_free_finite_X z i).1)
    (fun i ↦ (koszulComplex_free_finite_X z i).2) e (koszulComplex_isZero_X_of_lt z)
    (Ideal.span (Set.range z)).fg_of_isNoetherianRing
    (fun v _ q ↦ ordinary_koszul_pow_finite z v q)

end SerrePositivity.Section4
