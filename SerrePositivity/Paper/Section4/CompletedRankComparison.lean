module

public import SerrePositivity.Paper.Section4.UniformRepresentative
public import SerrePositivity.Paper.Section4.NormalizedRankComparison
public import SerrePositivity.Asymptotic.CompletedEulerComparison

/-!
# 冪等完備化後の任意の対象に対する命題4.5の Euler 比較

Koszul 完全性から A 側の一様代表を供給し、有限版3.5bを任意の直和因子に拡張する。
ここでの対象は支持つきランク商の Karoubi 包絡であり、
全体のランク商を冪等完備化した後の支持部分圏と既存の圏同値で対応する。
正規化側は直接の A → C を使う。二段の商関手との自然同型は
`Asymptotic/BaseChangeComposition` と `PaperBaseChange`、
論文の圏の K₀ への接続は `PaperK0Comparison` にある。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section4

open CategoryTheory CategoryTheory.Idempotents IsLocalRing Filter
open SerrePositivity.Asymptotic

/-- 冪等完備化した支持つきランク商上の通常の Euler 評価。 -/
noncomputable def ordinaryCompletedSupportedEuler
    {R : Type u} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (hArt : IsArtinianRing (R ⧸ Ideal.span (Set.range z)))
    {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) : ℝ := by
  letI := hArt
  exact completedSupportedEuler (NormalizedLength.ordinary R) Submodule.fg_bot z bot_le
    (fun v _ i ↦ ordinary_koszul_pow_finite z v i) U hU hs X

/-- 通常の評価の階数倍公式は、冪等完備化後の任意の対象で成り立つ。 -/
theorem ordinaryCompletedSupportedEuler_changeRing
    {A T : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Finite A T]
    {e : ℕ} (z : Fin e → A)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hχ : koszulEulerChar A T z = Module.finrank A T)
    {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    letI : IsNoetherianRing T := IsNoetherianRing.of_finite A T
    ordinaryCompletedSupportedEuler (algebraMap A T ∘ z)
      (isArtinianRing_quotient_span_of_finite A T z
        (by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical)) U hU hs
      (((functorExtension₂ _ _).obj (supportedRankChangeRing (algebraMap A T) z)).obj X) =
      (Module.finrank A T : ℝ) *
        ordinaryCompletedSupportedEuler z (isArtinianRing_quotient_span_of_eq hz) U hU hs X := by
  let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := supportedRank_isIdempotentComplete_of_koszul (s := s) z hz hKoszul
  dsimp only [ordinaryCompletedSupportedEuler]
  apply completedSupportedEuler_changeRing
  intro P hP
  simpa only [← chiOrd_eq_lambdaEuler_ordinary] using
    lemma_3_5b_ord_of_koszul hz hKoszul hres hχ P hP

/-- 正規化評価の階数倍公式も、冪等完備化後の任意の対象で成り立つ。 -/
theorem normalizedCompletedSupportedEuler_changeRing
    {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    [CommRing T] [Algebra A T] [Module.Finite A T]
    [CommRing C] [Nontrivial C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    {e : ℕ} (z : Fin e → A)
    (lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)))
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T)
    (hfin : ∀ v j : ℕ,
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (X : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    completedSupportedEuler lam ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C))
      (algebraMap A C ∘ z) (base_ideal_le_radical z hz)
      (fun v _ i ↦ base_koszul_pow_finite z lam hfin v i) U hU hs
      (((functorExtension₂ _ _).obj (supportedRankChangeRing (algebraMap A C) z)).obj X) =
      (Module.finrank A T : ℝ) *
        ordinaryCompletedSupportedEuler z (isArtinianRing_quotient_span_of_eq hz) U hU hs X := by
  have := supportedRank_isIdempotentComplete_of_koszul (s := s) z hz hKoszul
  dsimp only [ordinaryCompletedSupportedEuler]
  apply completedSupportedEuler_changeRing
  intro P hP
  simpa only [← chiOrd_eq_lambdaEuler_ordinary] using
    lambdaEuler_baseChange_eq_rank_mul z lam hz hKoszul hkz hq hfin P hP

end SerrePositivity.Section4
