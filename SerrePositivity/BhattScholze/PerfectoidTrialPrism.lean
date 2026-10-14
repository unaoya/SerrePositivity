module

public import SerrePositivity.BhattScholze.PerfectoidDistinguishedKernel
public import SerrePositivity.BhattScholze.PerfectDeltaPDQuotientEquiv

/-! # 任意の非零perfectoid試験環の完全prism商表示

標準Fontaine核を実PD完備化し、実H⁰の商比較で試験環を復元する。
Fontaine核進完備性や試験環のp正則性を仮定しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable (T : Type u) [CommRing T] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : T))] [IsAdicComplete (Ideal.span {(p : T)}) T]

/-- 四条件の非零枝から、具体的な実H⁰上の完全prismと試験環への商同型を得る。 -/
theorem exists_perfectoidTrialPrism
    (hF : Function.Surjective (fun x : ModP T p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta T p)).IsPrincipal)
    (π : T) (u : Tˣ) (hpEq : (p : T) = u * π ^ p) :
    ∃ (d : WittVector p (PreTilt T p))
      (hd : (wittDeltaStructure p (PreTilt T p)).IsDistinguished d),
      letI := pdCompletionCommRing (WittVector p (PreTilt T p)) p d
      ∃ e : PDCompletionH0 (WittVector p (PreTilt T p)) p d ⧸
          (perfectDeltaPDPrism (wittDeltaStructure p (PreTilt T p))
            (wittDeltaStructure_isPerfect p (PreTilt T p)) d hd).ideal ≃+* T,
        e.toRingHom.comp ((Ideal.Quotient.mk _).comp
          (pdCompletionUnit (WittVector p (PreTilt T p)) p d)) =
          WittVector.fontaineTheta T p := by
  obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator T p hF hker π u hpEq
  refine ⟨d, hd, ?_⟩
  let := pdCompletionCommRing (WittVector p (PreTilt T p)) p d
  exact exists_perfectDeltaPDQuotientEquiv (wittDeltaStructure p (PreTilt T p))
    (wittDeltaStructure_isPerfect p (PreTilt T p)) d hd (WittVector.fontaineTheta T p)
    (fun x ↦ surjective_fontaineTheta hF x) hk

end SerrePositivity.BhattScholze
