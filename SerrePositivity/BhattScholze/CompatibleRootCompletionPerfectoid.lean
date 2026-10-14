module

public import SerrePositivity.BhattScholze.CompatibleRootPDComparison
public import SerrePositivity.BhattScholze.CompatibleRootTilt
public import SerrePositivity.BhattScholze.PerfectoidDistinguishedKernel

/-! # B4a：根付き単項商の完備化のperfectoid性

tiltの根イデアル商のWitt環を実PD完備化し、標準射を両立させて古典的候補と比較する。
Andréの引用・一般全射性・B5を使わない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- perfectoid環の両立する根をすべて消した商のp完備化はperfectoid。
一般のpねじれと零環も含む。 -/
theorem compatibleRootCompletion_isIntegralPerfectoid
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    IsIntegralPerfectoid (CompatibleRootCompletion p ρ) p := by
  let C := CompatibleRootCompletion p ρ
  let qR := (compatibleRootCompletionMap p ρ).comp (Ideal.Quotient.mk (Ideal.span {ρ 0}))
  rcases subsingleton_or_nontrivial C with hsC | hnC
  · exact Or.inl hsC
  · let := hnC
    rcases hR with hsR | ⟨hpR, hcR, ⟨π, u, hu⟩, hFR, hkerR⟩
    · let := hsR
      let : Subsingleton C := qR.codomain_trivial
      exact Or.inl inferInstance
    · let := hcR
      have hR : IsIntegralPerfectoid R p := Or.inr ⟨hpR, hcR, ⟨π, u, hu⟩, hFR, hkerR⟩
      let : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
      let := compatibleRootCompletion_isAdicComplete (p := p) ρ
      have hpC : ¬ IsUnit (p : C) := by
        intro h
        let : Subsingleton C := subsingleton_of_isUnit_natCast_of_isHausdorff p C h
        exact zero_ne_one (Subsingleton.elim (0 : C) 1)
      let : Fact (¬ IsUnit (p : C)) := ⟨hpC⟩
      let k := PreTilt R p
      let κ := compatibleRootTilt ρ hρ
      let K := compatibleRootIdeal κ
      let Q := k ⧸ K
      let qk := Ideal.Quotient.mk K
      let L := Perfection.map p (modPMap p qR)
      have hqρ : ∀ n, qR (ρ n) = 0 := by
        intro n
        change algebraMap (R ⧸ compatibleRootIdeal ρ) C
          (Ideal.Quotient.mk (compatibleRootIdeal ρ) (ρ n)) = 0
        have hz : Ideal.Quotient.mk (compatibleRootIdeal ρ) (ρ n) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr Ideal.mem_span_range_self
        rw [hz, map_zero]
      have hKL : K ≤ RingHom.ker L := compatibleRootTiltIdeal_le_ker ρ hρ qR hqρ
      let LQ : Q →+* PreTilt C p := Ideal.Quotient.lift K L hKL
      let : Nontrivial (PreTilt C p) := CharP.nontrivial_of_char_ne_one
        (R := PreTilt C p) (Fact.out : p.Prime).ne_one
      let : Nontrivial Q := LQ.domain_nontrivial
      have hpQ : (p : Q) = 0 := by
        rw [← map_natCast qk, CharP.cast_eq_zero, map_zero]
      let : CharP Q p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpQ
      let : PerfectRing Q p := compatibleRootTiltQuotient_perfectRing ρ hρ
      let w : WittVector p k →+* WittVector p Q := WittVector.map qk
      have hw : Function.Surjective w := WittVector.map_surjective _ Ideal.Quotient.mk_surjective
      obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator R p hFR hkerR π u hu
      let D := wittDeltaStructure p Q
      have hD := wittDeltaStructure_isPerfect p Q
      have hdw : D.IsDistinguished (w d) :=
        (wittDeltaStructure_map_isDeltaHom p k qk).map_isDistinguished hd
      let β : WittVector p Q →+* C :=
        (WittVector.fontaineTheta C p).comp (WittVector.map LQ)
      have hβ : β.comp w = qR.comp (WittVector.fontaineTheta R p) := by
        have hL : LQ.comp qk = L := rfl
        have hm : (WittVector.map LQ).comp w = WittVector.map L := by
          ext x n
          change LQ (qk (x.coeff n)) = L (x.coeff n)
          exact RingHom.congr_fun hL _
        change ((WittVector.fontaineTheta C p).comp (WittVector.map LQ)).comp w = _
        rw [RingHom.comp_assoc, hm]
        exact fontaineTheta_natural p qR
      let a : WittVector p k := WittVector.teichmuller p (κ 0)
      have ha : WittVector.fontaineTheta R p a = ρ 0 := by
        rw [WittVector.fontaineTheta_teichmuller, compatibleRootTilt_untilt]
      have hwa : w a = 0 := by
        change WittVector.map qk (WittVector.teichmuller p (κ 0)) = 0
        rw [WittVector.map_teichmuller]
        have hqκ : qk (κ 0) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr Ideal.mem_span_range_self
        rw [hqκ, WittVector.teichmuller_zero]
      let := pdCompletionCommRing (WittVector p Q) p (w d)
      obtain ⟨e, _⟩ := exists_compatibleRootCompletionPDQuotientEquiv hR ρ hρ D hD d
        (WittVector.fontaineTheta R p) (fun x ↦ surjective_fontaineTheta hFR x) hk
        w hw hdw β hβ a ha hwa
      have hU := (perfectDeltaPDPrism D hD (w d) hdw).quotient_isIntegralPerfectoid
        (perfectDeltaPDPrism_isPerfect D hD (w d) hdw)
      exact isIntegralPerfectoid_of_ringEquiv p e.symm hU

/-- 根を持つ単項商の具体的標準射はperfectoid化。 -/
theorem compatibleRootCompletionMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    IsPerfectoidization p (compatibleRootCompletionMap p ρ) :=
  compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ
    (compatibleRootCompletion_isIntegralPerfectoid hR ρ hρ)

/-- 根付き単項商の任意の普遍perfectoid化は全射。 -/
theorem surjective_of_isPerfectoidization_of_compatibleRoots_unconditional
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {C : Type u} [CommRing C] (f : R ⧸ Ideal.span {ρ 0} →+* C)
    (hf : IsPerfectoidization p f) : Function.Surjective f :=
  surjective_of_isPerfectoidization_of_compatibleRoots hR ρ hρ
    (compatibleRootCompletion_isIntegralPerfectoid hR ρ hρ) f hf

end SerrePositivity.BhattScholze
