module

public import SerrePositivity.Asymptotic.SupportedCompletedRepresentative
public import SerrePositivity.Paper.Section4.KoszulInputs

/-!
# §4 の A 側の一様自由代表

極大イデアルを生成する列の Koszul 完全性から、
支持つきランク商の冪等完備性と、冪等完備化後の任意の支持対象の
実際の共通有界自由複体列による表示を得る。
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

include hz hKoszul in
/-- S5：冪等完備化後の支持対象は、一様に支持された共通有界自由複体列で表せる。 -/
theorem uniform_free_representative_of_koszul
    (X : CompletedSequenceRankQuotient A s) (hX : supportedCompletedRankQuotient z X) :
    ∃ (P : CochainComplex (FreeSequence A s) ℤ)
      (hP : strictlyBoundedComplex (FreeSequence A s) P),
      supportedSequence z (sequenceHomotopyObj P hP) ∧
      Nonempty ((toKaroubi _).obj
        (sequenceRankQuotientFunctor.obj (sequenceHomotopyObj P hP)) ≅ X) := by
  have hres : IsResolutionOf (koszulComplex z) (ModuleCat.of A (A ⧸ maximalIdeal A)) := by
    have h := isResolutionOf_koszul z hKoszul
    rw [hz] at h
    exact h
  have := isArtinianRing_quotient_span_of_eq hz
  exact supportedCompleted_has_complex_representative z (koszulComplex z) hres
    (fun i ↦ (koszulComplex_free_finite_X z i).1)
    (fun i ↦ (koszulComplex_free_finite_X z i).2) e (koszulComplex_isZero_X_of_lt z)
    (Ideal.span (Set.range z)).fg_of_isNoetherianRing
    (fun v _ q ↦ ordinary_koszul_pow_finite z v q) X hX

end SerrePositivity.Section4
