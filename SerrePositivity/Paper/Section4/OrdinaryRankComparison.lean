module

public import SerrePositivity.Paper.Section4.RepresentativeComparison

/-!
# 冪等完備化前のランク商での通常の Euler 評価と比較

有限なパラメータ商から Koszul 有限性を供給して、実際の `K₀` 上に通常の評価を作る。
有限版3.5bを使い、基底変更後の評価が階数倍になることをこの群全体で証明する。
命題4.5に必要な冪等完備化後の群への拡張は、別途証明する必要がある。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section4

open CategoryTheory IsLocalRing Filter
open SerrePositivity.Asymptotic

/-- 通常の長さにより定まる、支持つきランク商の Grothendieck 群上の評価。 -/
noncomputable def ordinaryRankEulerK0
    {R : Type u} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (hArt : IsArtinianRing (R ⧸ Ideal.span (Set.range z)))
    {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n) :
    TriangulatedK0 (SupportedSequenceRankQuotient (s := s) z) →+ ℝ := by
  letI := hArt
  exact supportedRankEulerK0 (NormalizedLength.ordinary R) Submodule.fg_bot z bot_le
    (fun v _ i ↦ ordinary_koszul_pow_finite z v i) U hU hs

/-- 通常の評価の階数倍公式は、冪等完備化前の支持つきランク商の `K₀` 全体で成り立つ。 -/
theorem ordinaryRankEulerK0_changeRing
    {A T : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Finite A T]
    {e : ℕ} (z : Fin e → A)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hχ : koszulEulerChar A T z = Module.finrank A T)
    {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n) :
    letI : IsNoetherianRing T := IsNoetherianRing.of_finite A T
    (ordinaryRankEulerK0 (algebraMap A T ∘ z)
      (isArtinianRing_quotient_span_of_finite A T z
        (by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical)) U hU hs).comp
      (TriangulatedK0.map (supportedRankChangeRing (algebraMap A T) z)) =
        (Module.finrank A T : ℝ) •
          ordinaryRankEulerK0 z (isArtinianRing_quotient_span_of_eq hz) U hU hs := by
  let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  dsimp only [ordinaryRankEulerK0]
  apply supportedRankEulerK0_changeRing
  intro P hP
  simpa only [← chiOrd_eq_lambdaEuler_ordinary] using
    lemma_3_5b_ord_of_koszul hz hKoszul hres hχ P hP

end SerrePositivity.Section4
