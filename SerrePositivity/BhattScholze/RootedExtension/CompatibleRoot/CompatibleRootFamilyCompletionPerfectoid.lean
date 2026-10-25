module

public import SerrePositivity.BhattScholze.RootedExtension.CompatibleRoot.CompatibleRootFamilyPDComparison
public import SerrePositivity.BhattScholze.RootedExtension.CompatibleRoot.CompatibleRootTilt
public import SerrePositivity.BhattScholze.Prism.PerfectoidDistinguishedKernel

/-! # B4-4：任意根族の商の完備化のperfectoid性

tiltの根イデアル商のWitt環を実PD完備化し、標準射を両立させて古典的候補と比較する。
Andréの引用・一般全射性・B5を使わない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type u}

/-- perfectoid環の両立する根をすべて消した商のp完備化はperfectoid。
一般のpねじれと零環も含む。 -/
theorem compatibleRootFamilyCompletion_isIntegralPerfectoid
    (hR : IsIntegralPerfectoid R p) (ρ : σ → ℕ → R)
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n) :
    IsIntegralPerfectoid (CompatibleRootFamilyCompletion p ρ) p := by
  let C := CompatibleRootFamilyCompletion p ρ
  let qR := (compatibleRootFamilyCompletionMap p ρ).comp
    (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ))
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
      let := compatibleRootFamilyCompletion_isAdicComplete (p := p) ρ
      have hpC : ¬ IsUnit (p : C) := by
        intro h
        let : Subsingleton C := subsingleton_of_isUnit_natCast_of_isHausdorff p C h
        exact zero_ne_one (Subsingleton.elim (0 : C) 1)
      let : Fact (¬ IsUnit (p : C)) := ⟨hpC⟩
      let k := PreTilt R p
      let κ := fun s ↦ compatibleRootTilt (ρ s) (hρ s)
      let K := compatibleRootFamilyIdeal κ
      let Q := k ⧸ K
      let qk := Ideal.Quotient.mk K
      let L := Perfection.map p (modPMap p qR)
      have hqρ : ∀ s n, qR (ρ s n) = 0 := by
        intro s n
        change algebraMap (R ⧸ compatibleRootFamilyIdeal ρ) C
          (Ideal.Quotient.mk (compatibleRootFamilyIdeal ρ) (ρ s n)) = 0
        have hz : Ideal.Quotient.mk (compatibleRootFamilyIdeal ρ) (ρ s n) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(s, n), rfl⟩)
        rw [hz, map_zero]
      have hKL : K ≤ RingHom.ker L := by
        apply Ideal.span_le.mpr
        rintro _ ⟨⟨s, n⟩, rfl⟩
        exact compatibleRootTiltIdeal_le_ker (ρ s) (hρ s) qR (hqρ s)
          (Ideal.mem_span_range_self (x := n))
      let LQ : Q →+* PreTilt C p := Ideal.Quotient.lift K L hKL
      let : Nontrivial (PreTilt C p) := CharP.nontrivial_of_char_ne_one
        (R := PreTilt C p) (Fact.out : p.Prime).ne_one
      let : Nontrivial Q := LQ.domain_nontrivial
      have hpQ : (p : Q) = 0 := by
        rw [← map_natCast qk, CharP.cast_eq_zero, map_zero]
      let : CharP Q p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpQ
      let : PerfectRing Q p := compatibleRootFamilyQuotient_perfectRing κ
        (fun s n ↦ compatibleRootTilt_pow (ρ s) (hρ s) n)
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
      let a : σ → WittVector p k := fun s ↦ WittVector.teichmuller p (κ s 0)
      have ha : ∀ s, WittVector.fontaineTheta R p (a s) = ρ s 0 := by
        intro s
        rw [WittVector.fontaineTheta_teichmuller, compatibleRootTilt_untilt]
      have hwa : ∀ s, w (a s) = 0 := by
        intro s
        change WittVector.map qk (WittVector.teichmuller p (κ s 0)) = 0
        rw [WittVector.map_teichmuller]
        have hqκ : qk (κ s 0) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(s, 0), rfl⟩)
        rw [hqκ, WittVector.teichmuller_zero]
      let := pdCompletionCommRing (WittVector p Q) p (w d)
      obtain ⟨e, _⟩ := exists_compatibleRootFamilyCompletionPDQuotientEquiv hR ρ hρ D hD d
        (WittVector.fontaineTheta R p) (fun x ↦ surjective_fontaineTheta hFR x) hk
        w hw hdw β hβ a ha hwa
      have hU := (perfectDeltaPDPrism D hD (w d) hdw).quotient_isIntegralPerfectoid
        (perfectDeltaPDPrism_isPerfect D hD (w d) hdw)
      exact isIntegralPerfectoid_of_ringEquiv p e.symm hU

/-- 任意根族の最初の元の商の具体的標準射はperfectoid化。 -/
theorem compatibleRootFamilyCompletionMap_isPerfectoidization
    (hR : IsIntegralPerfectoid R p) (ρ : σ → ℕ → R)
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n) :
    IsPerfectoidization p (compatibleRootFamilyCompletionMap p ρ) :=
  compatibleRootFamilyCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ
    (compatibleRootFamilyCompletion_isIntegralPerfectoid hR ρ hρ)

/-- 任意根族の最初の元の商の任意の普遍perfectoid化は全射。 -/
theorem surjective_of_isPerfectoidization_of_compatibleRootFamily
    (hR : IsIntegralPerfectoid R p) (ρ : σ → ℕ → R)
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    {C : Type u} [CommRing C] (f : R ⧸ compatibleRootFamilyZeroIdeal ρ →+* C)
    (hf : IsPerfectoidization p f) : Function.Surjective f := by
  let := hR.isAdicComplete R p
  have h := compatibleRootFamilyCompletionMap_isPerfectoidization hR ρ hρ
  exact (h.surjective_iff p hf).mp (compatibleRootFamilyCompletionMap_surjective ρ)

end SerrePositivity.BhattScholze
