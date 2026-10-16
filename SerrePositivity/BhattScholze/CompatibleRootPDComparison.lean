module

public import SerrePositivity.BhattScholze.CompatibleRootCompletionSurjective
public import SerrePositivity.BhattScholze.PerfectPrismQuotientPerfectoid
public import SerrePositivity.BhattScholze.PerfectDeltaPDQuotientComparison

/-! # B4-3：古典的根イデアル商の完備化と実PD完備化商の比較

具体的な標準射の図式と全射性から比較同型を証明する。
古典的完備化と実導来完備化を無条件に同一視しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

omit [Fact p.Prime] in
/-- 根イデアル商の古典的p完備化は、自身のp作用についてp完備。 -/
theorem compatibleRootCompletion_isAdicComplete (ρ : ℕ → R) :
    IsAdicComplete (Ideal.span {(p : CompatibleRootCompletion p ρ)})
      (CompatibleRootCompletion p ρ) := by
  let Q := R ⧸ compatibleRootIdeal ρ
  let I : Ideal Q := Ideal.span {(p : Q)}
  have h := AdicCompletion.isAdicComplete (M := Q) (Submodule.fg_span_singleton (p : Q))
  have hm : I.map (algebraMap Q (AdicCompletion I Q)) =
      Ideal.span {(p : AdicCompletion I Q)} :=
    pIdeal_map Q (AdicCompletion I Q) p (algebraMap Q (AdicCompletion I Q))
  rw [← hm]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr h

/-- 根を消すWitt型商と実PD完備化の具体的図式から、古典的候補との比較同型を得る。 -/
theorem exists_compatibleRootCompletionPDQuotientEquiv
    (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (D : DeltaStructure p B) (hD : D.IsPerfect) (d : A)
    (θ : A →+* R) (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {d})
    (w : A →+* B) (hw : Function.Surjective w) (hd : D.IsDistinguished (w d))
    (β : B →+* CompatibleRootCompletion p ρ)
    (hβ : β.comp w = ((compatibleRootCompletionMap p ρ).comp
      (Ideal.Quotient.mk (Ideal.span {ρ 0}))).comp θ)
    (a : A) (ha : θ a = ρ 0) (hwa : w a = 0) :
    letI := pdCompletionCommRing B p (w d)
    ∃ e : CompatibleRootCompletion p ρ ≃+*
        PDCompletionH0 B p (w d) ⧸ Ideal.span {pdCompletionUnit B p (w d) (w d)},
      e.toRingHom.comp ((compatibleRootCompletionMap p ρ).comp
        (Ideal.Quotient.mk (Ideal.span {ρ 0}))) =
        θ.liftOfSurjective hθ ⟨(Ideal.Quotient.mk _).comp
          ((pdCompletionUnit B p (w d)).comp w), by
            rw [hker, Ideal.span_singleton_le_iff_mem]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩ := by
  let := pdCompletionCommRing B p (w d)
  let := hR.isAdicComplete R p
  let := compatibleRootCompletion_isAdicComplete (p := p) ρ
  let qR := (compatibleRootCompletionMap p ρ).comp (Ideal.Quotient.mk (Ideal.span {ρ 0}))
  have hqR : Function.Surjective qR :=
    (compatibleRootCompletionMap_surjective (p := p) ρ).comp Ideal.Quotient.mk_surjective
  have hI : Ideal.span {ρ 0} ≤ (RingHom.ker w).map θ := by
    rw [Ideal.span_singleton_le_iff_mem, ← ha]
    exact Ideal.mem_map_of_mem θ (show a ∈ RingHom.ker w from hwa)
  have hExtend : ∀ (T : Type u) [CommRing T], IsIntegralPerfectoid T p →
      ∀ i : R →+* T, Ideal.span {ρ 0} ≤ RingHom.ker i →
        ∃ c : CompatibleRootCompletion p ρ →+* T, c.comp qR = i := by
    intro T _ hT i hi
    let i0 := Ideal.Quotient.lift (Ideal.span {ρ 0}) i hi
    obtain ⟨c, hc, _⟩ := existsUnique_compatibleRootCompletionLift_to_perfectoid ρ hρ hT i0
    refine ⟨c, ?_⟩
    change c.comp ((compatibleRootCompletionMap p ρ).comp
      (Ideal.Quotient.mk (Ideal.span {ρ 0}))) = i
    rw [← RingHom.comp_assoc, hc]
    rfl
  exact exists_perfectDeltaPDQuotientEquiv_of_perfectoidExtension D hD d θ hθ hker
    w hw hd (Ideal.span {ρ 0}) hI qR hqR hExtend β hβ

end SerrePositivity.BhattScholze
