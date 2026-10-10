module

public import SerrePositivity.Asymptotic.CompletedEulerComparison
public import SerrePositivity.Asymptotic.CompletedEulerAdditivity
public import SerrePositivity.Asymptotic.BaseChangeComposition

/-! # 冪等完備化後の K₀ 上の階数倍公式 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 1024

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} {J : Ideal R} {I : Ideal S}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

/-- 一様自由代表を介して得た全対象の比較を、K₀ の準同型の等式へ移す。 -/
theorem completedSupportedEulerK0_changeRing
    [IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z)]
    (φ : R →+* S) (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ q,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology q) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (c : ℝ)
    (hc : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ), IsPerfectSupported z P →
      lambdaEuler mu (baseChange φ P) = c * lambdaEuler lam P) :
    (completedSupportedEulerK0 mu hIfg (φ ∘ z) hI hfinS U hU hs).comp
      (TriangulatedK0.map ((functorExtension₂ _ _).obj (supportedRankChangeRing φ z))) =
        c • completedSupportedEulerK0 lam hfg z hJ hfin U hU hs := by
  apply TriangulatedK0.hom_ext
  intro X
  simpa only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    completedSupportedEulerK0_mk, AddMonoidHom.smul_apply, smul_eq_mul] using
      completedSupportedEuler_changeRing lam hfg z hJ hfin φ mu hIfg hI hfinS U hU hs c hc X

end SerrePositivity.Asymptotic
