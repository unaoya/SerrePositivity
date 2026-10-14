module

public import SerrePositivity.BhattScholze.CompatibleRootCompletionSurjective
public import SerrePositivity.BhattScholze.PerfectPrismQuotientPerfectoid
public import SerrePositivity.BhattScholze.PDCompletionInterface

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
      Ideal.span {(p : AdicCompletion I Q)} := by
    rw [Ideal.map_span, Set.image_singleton]
    have he : algebraMap Q (AdicCompletion I Q) (p : Q) = (p : AdicCompletion I Q) :=
      map_natCast _ p
    exact congrArg (fun x ↦ Ideal.span {x}) he
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
  let H := PDCompletionH0 B p (w d)
  let j := pdCompletionUnit B p (w d)
  let U := H ⧸ Ideal.span {j (w d)}
  let qU := Ideal.Quotient.mk (Ideal.span {j (w d)})
  let C := CompatibleRootCompletion p ρ
  let qR := (compatibleRootCompletionMap p ρ).comp (Ideal.Quotient.mk (Ideal.span {ρ 0}))
  let := hR.isAdicComplete R p
  let := compatibleRootCompletion_isAdicComplete (p := p) ρ
  let := perfectDeltaPDPrism_quotient_isAdicComplete D hD (w d) hd
  let i : R →+* U := θ.liftOfSurjective hθ ⟨qU.comp (j.comp w), by
    rw [hker, Ideal.span_singleton_le_iff_mem]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩
  have hiθ : i.comp θ = qU.comp (j.comp w) := θ.liftOfSurjective_comp hθ _
  have hiρ : i (ρ 0) = 0 := by
    rw [← ha]
    have hh : i (θ a) = qU (j (w a)) := RingHom.congr_fun hiθ a
    rw [hh, hwa, map_zero, map_zero]
  let i0 := Ideal.Quotient.lift (Ideal.span {ρ 0}) i (by
    change Ideal.span {ρ 0} ≤ RingHom.ker i
    rw [Ideal.span_singleton_le_iff_mem]
    exact hiρ)
  have hU : IsIntegralPerfectoid U p :=
    (perfectDeltaPDPrism D hD (w d) hd).quotient_isIntegralPerfectoid
      (perfectDeltaPDPrism_isPerfect D hD (w d) hd)
  obtain ⟨c, hc, _⟩ := existsUnique_compatibleRootCompletionLift_to_perfectoid ρ hρ hU i0
  have hcR : c.comp qR = i := by
    change c.comp ((compatibleRootCompletionMap p ρ).comp
      (Ideal.Quotient.mk (Ideal.span {ρ 0}))) = i
    rw [← RingHom.comp_assoc, hc]
    rfl
  have hθd : θ d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.mem_span_singleton_self _
  have hβd : β (w d) = 0 := by
    have hh : β (w d) = qR (θ d) := RingHom.congr_fun hβ d
    rw [hh, hθd, map_zero]
  have hz (T : Type u) [CommRing T] : IsModuleComplete T (0 : T) (ModuleCat.of T T) := by
    rw [isModuleComplete_iff_recurrence_bijective]
    change Function.Bijective (fun x : ℕ → T ↦ fun n ↦ x n - (0 : T) • x (n + 1))
    simp only [zero_smul, sub_zero]
    exact ⟨fun x y h ↦ funext (fun n ↦ congrFun h n), fun x ↦ ⟨x, rfl⟩⟩
  have hpC := isModuleComplete_of_isAdicComplete C (p : C) (ModuleCat.of C C)
  have hdC : IsModuleComplete C (β (w d)) (ModuleCat.of C C) := hβd ▸ hz C
  obtain ⟨b, hb, _⟩ := existsUnique_pdCompletionRingHom B p (w d) C β hpC hdC
  let b0 : U →+* C := Ideal.Quotient.lift _ b (by
    change Ideal.span {j (w d)} ≤ RingHom.ker b
    rw [Ideal.span_singleton_le_iff_mem]
    have hh : b (j (w d)) = β (w d) := RingHom.congr_fun hb (w d)
    exact hh.trans hβd)
  have hbq : b0.comp qU = b := rfl
  have hbi : b0.comp i = qR := by
    apply RingHom.ext
    intro r
    obtain ⟨x, rfl⟩ := hθ r
    have hh : i (θ x) = qU (j (w x)) := RingHom.congr_fun hiθ x
    change b0 (i (θ x)) = qR (θ x)
    rw [hh]
    exact (RingHom.congr_fun hb (w x)).trans (RingHom.congr_fun hβ x)
  have hbc : b0.comp c = RingHom.id C := by
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := (compatibleRootCompletionMap_surjective (p := p) ρ).comp
      Ideal.Quotient.mk_surjective x
    change b0 (c (qR r)) = qR r
    have hh : c (qR r) = i r := RingHom.congr_fun hcR r
    rw [hh]
    exact RingHom.congr_fun hbi r
  have hcb : c.comp b0 = RingHom.id U := by
    apply Ideal.Quotient.ringHom_ext
    have hcbβ : c.comp β = qU.comp j := by
      apply RingHom.ext
      intro y
      obtain ⟨x, rfl⟩ := hw y
      have hh : β (w x) = qR (θ x) := RingHom.congr_fun hβ x
      change c (β (w x)) = qU (j (w x))
      rw [hh]
      exact (RingHom.congr_fun hcR (θ x)).trans (RingHom.congr_fun hiθ x)
    have hpU := isModuleComplete_of_isAdicComplete U (p : U) (ModuleCat.of U U)
    have hqd : (qU.comp j) (w d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    have hdU : IsModuleComplete U ((qU.comp j) (w d)) (ModuleCat.of U U) := hqd ▸ hz U
    have he : c.comp b = qU := by
      apply pdCompletionRingHom_ext B p (w d) U (qU.comp j) hpU hdU
      · rw [RingHom.comp_assoc, hb, hcbβ]
      · rfl
    change (c.comp b0).comp qU = (RingHom.id U).comp qU
    rw [RingHom.comp_assoc, hbq, he, RingHom.id_comp]
  refine ⟨{ c with
    invFun := b0
    left_inv := RingHom.congr_fun hbc
    right_inv := RingHom.congr_fun hcb }, hcR⟩

end SerrePositivity.BhattScholze
