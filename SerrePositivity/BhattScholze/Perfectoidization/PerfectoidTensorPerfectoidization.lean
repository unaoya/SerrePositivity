module

public import SerrePositivity.BhattScholze.Prism.WittPresentedPerfectoidTensorModP
public import SerrePositivity.BhattScholze.Prism.PerfectoidWittBasePresentation
public import SerrePositivity.BhattScholze.Prism.PerfectoidDistinguishedKernel

/-! # B4-5：任意perfectoid環の通常テンソルのperfectoid化

標準Fontaine表示と自然性を実際のperfectoid入力から供給する。
基底・両因子・係数テンソルの零環の場合も含む。mod p比較は別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct

/-- perfectoid環R上の任意のperfectoid環S,Tの通常テンソルにはperfectoid化が存在する。
有限性・p正則性・非零性を要求しない。 -/
theorem exists_perfectoidTensorPerfectoidization_modP (p : ℕ) [Fact p.Prime]
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    ∃ (E : Type u) (_ : CommRing E) (F : S ⊗[R] T →+* E),
      IsPerfectoidization p F ∧ Function.Bijective (modPMap p F) := by
  rcases subsingleton_or_nontrivial (S ⊗[R] T) with hzero | hn
  · let := hzero
    refine ⟨S ⊗[R] T, inferInstance, RingHom.id _, ⟨Or.inl hzero, ?_⟩, ?_⟩
    · intro D _ _ g
      refine ⟨g, RingHom.comp_id g, ?_⟩
      intro L hL
      simpa only [RingHom.comp_id] using hL
    · exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
        fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩
  · let := hn
    let : Nontrivial R := (algebraMap R (S ⊗[R] T)).domain_nontrivial
    let : Nontrivial S :=
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom.domain_nontrivial
    let : Nontrivial T :=
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom.domain_nontrivial
    rcases hR with hzero | ⟨hpR, hcR, ⟨π, u, hpEq⟩, hFR, hkerR⟩
    · let := hzero
      exact (zero_ne_one (Subsingleton.elim (0 : R) 1)).elim
    rcases hS with hzero | ⟨hpS, hcS, _, hFS, hkerS⟩
    · let := hzero
      exact (zero_ne_one (Subsingleton.elim (0 : S) 1)).elim
    rcases hT with hzero | ⟨hpT, hcT, _, hFT, hkerT⟩
    · let := hzero
      exact (zero_ne_one (Subsingleton.elim (0 : T) 1)).elim
    let : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
    let : Fact (¬ IsUnit (p : S)) := ⟨hpS⟩
    let : Fact (¬ IsUnit (p : T)) := ⟨hpT⟩
    let := hcR
    let := hcS
    let := hcT
    obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator R p
      hFR hkerR π u hpEq
    have hzero : WittVector.fontaineTheta R p d = 0 := by
      apply RingHom.mem_ker.mp
      rw [hk]
      exact Ideal.mem_span_singleton_self _
    let kR := PreTilt R p
    let kS := PreTilt S p
    let kT := PreTilt T p
    let : Algebra kR kS := (Perfection.map p (modPMap p (algebraMap R S))).toAlgebra
    let : Algebra kR kT := (Perfection.map p (modPMap p (algebraMap R T))).toAlgebra
    let eS := fontaineBaseWittQuotientEquiv p (algebraMap R S) d hd hzero hFS hkerS
    let eT := fontaineBaseWittQuotientEquiv p (algebraMap R T) d hd hzero hFT hkerT
    have heS : (eS.toRingHom.comp (Ideal.Quotient.mk _)).comp
        (WittVector.map (algebraMap kR kS)) =
        (algebraMap R S).comp (WittVector.fontaineTheta R p) := by
      rw [fontaineBaseWittQuotientEquiv_comp_mk]
      exact fontaineTheta_natural p (algebraMap R S)
    have heT : (eT.toRingHom.comp (Ideal.Quotient.mk _)).comp
        (WittVector.map (algebraMap kR kT)) =
        (algebraMap R T).comp (WittVector.fontaineTheta R p) := by
      rw [fontaineBaseWittQuotientEquiv_comp_mk]
      exact fontaineTheta_natural p (algebraMap R T)
    obtain ⟨F, _, _, hF, hbij⟩ := exists_wittPresentedTensorPerfectoidization_modP p kR kS kT d hd
      (WittVector.fontaineTheta R p) (fun x ↦ surjective_fontaineTheta hFR x) eS eT heS heT
    exact ⟨WittCoefficientPushout p kR kS kT d, inferInstance, F, hF, hbij⟩

/-- 任意perfectoid環の通常テンソルのperfectoid化の存在。 -/
theorem exists_perfectoidTensorPerfectoidization (p : ℕ) [Fact p.Prime]
    (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    ∃ (E : Type u) (_ : CommRing E) (F : S ⊗[R] T →+* E), IsPerfectoidization p F := by
  obtain ⟨E, hE, F, hF, _⟩ := exists_perfectoidTensorPerfectoidization_modP p R S T hR hS hT
  exact ⟨E, hE, F, hF⟩

end SerrePositivity.BhattScholze
