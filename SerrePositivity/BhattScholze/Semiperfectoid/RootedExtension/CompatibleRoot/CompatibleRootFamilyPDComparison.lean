module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootFamilyQuotient
public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaPDQuotientComparison

/-! # B4-4：任意根族の完備化と実PD商の比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable {σ : Type u}

omit [Fact p.Prime] in
/-- 任意根族商の完備化は、自身のp作用についてp完備。 -/
theorem compatibleRootFamilyCompletion_isAdicComplete (ρ : σ → ℕ → R) :
    IsAdicComplete (Ideal.span {(p : CompatibleRootFamilyCompletion p ρ)})
      (CompatibleRootFamilyCompletion p ρ) := by
  let Q := R ⧸ compatibleRootFamilyIdeal ρ
  let I : Ideal Q := Ideal.span {(p : Q)}
  have h := AdicCompletion.isAdicComplete (M := Q) (Submodule.fg_span_singleton (p : Q))
  have hm : I.map (algebraMap Q (AdicCompletion I Q)) =
      Ideal.span {(p : AdicCompletion I Q)} :=
    pIdeal_map Q (AdicCompletion I Q) p (algebraMap Q (AdicCompletion I Q))
  rw [← hm]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr h

/-- 全根族を消す具体的なWitt型商から、古典的候補と実PD商の比較同型を得る。 -/
theorem exists_compatibleRootFamilyCompletionPDQuotientEquiv
    (hR : IsIntegralPerfectoid R p)
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (D : DeltaStructure p B) (hD : D.IsPerfect) (d : A)
    (θ : A →+* R) (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {d})
    (w : A →+* B) (hw : Function.Surjective w) (hd : D.IsDistinguished (w d))
    (β : B →+* CompatibleRootFamilyCompletion p ρ)
    (hβ : β.comp w = ((compatibleRootFamilyCompletionMap p ρ).comp
      (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ))).comp θ)
    (a : σ → A) (ha : ∀ s, θ (a s) = ρ s 0) (hwa : ∀ s, w (a s) = 0) :
    letI := pdCompletionCommRing B p (w d)
    ∃ e : CompatibleRootFamilyCompletion p ρ ≃+*
        PDCompletionH0 B p (w d) ⧸ Ideal.span {pdCompletionUnit B p (w d) (w d)},
      e.toRingHom.comp ((compatibleRootFamilyCompletionMap p ρ).comp
        (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ))) =
        θ.liftOfSurjective hθ ⟨(Ideal.Quotient.mk _).comp
          ((pdCompletionUnit B p (w d)).comp w), by
            rw [hker, Ideal.span_singleton_le_iff_mem]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩ := by
  let := pdCompletionCommRing B p (w d)
  let := hR.isAdicComplete R p
  let := compatibleRootFamilyCompletion_isAdicComplete (p := p) ρ
  let qR := (compatibleRootFamilyCompletionMap p ρ).comp
    (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ))
  have hqR : Function.Surjective qR :=
    (compatibleRootFamilyCompletionMap_surjective (p := p) ρ).comp Ideal.Quotient.mk_surjective
  have hI : compatibleRootFamilyZeroIdeal ρ ≤ (RingHom.ker w).map θ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change ρ s 0 ∈ (RingHom.ker w).map θ
    rw [← ha s]
    exact Ideal.mem_map_of_mem θ (show a s ∈ RingHom.ker w from hwa s)
  have hExtend : ∀ (T : Type u) [CommRing T], IsIntegralPerfectoid T p →
      ∀ i : R →+* T, compatibleRootFamilyZeroIdeal ρ ≤ RingHom.ker i →
        ∃ c : CompatibleRootFamilyCompletion p ρ →+* T, c.comp qR = i := by
    intro T _ hT i hi
    let i0 := Ideal.Quotient.lift (compatibleRootFamilyZeroIdeal ρ) i hi
    obtain ⟨c, hc, _⟩ := existsUnique_compatibleRootFamilyCompletionLift_to_perfectoid
      ρ hρ hT i0
    refine ⟨c, ?_⟩
    change c.comp ((compatibleRootFamilyCompletionMap p ρ).comp
      (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ))) = i
    rw [← RingHom.comp_assoc, hc]
    rfl
  exact exists_perfectDeltaPDQuotientEquiv_of_perfectoidExtension D hD d θ hθ hker
    w hw hd (compatibleRootFamilyZeroIdeal ρ) hI qR hqR hExtend β hβ

end SerrePositivity.BhattScholze
