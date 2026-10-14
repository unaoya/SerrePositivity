module

public import SerrePositivity.BhattScholze.PerfectPrismQuotientPerfectoid
public import SerrePositivity.BhattScholze.PerfectDeltaPDPrism
public import SerrePositivity.BhattScholze.PDCompletionInterface

/-! # B4の商比較の共通部分

完全prism商への射が延長する完備な全射候補と、実PD完備化商を比較する。
単項と任意根族で同じ比較証明を共有するためのBS専用補題。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R A B C : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing C]

/-- 完備な全射候補のperfectoid試験環への延長性から、実PD商との比較同型を得る。 -/
theorem exists_perfectDeltaPDQuotientEquiv_of_perfectoidExtension
    [IsAdicComplete (Ideal.span {(p : C)}) C]
    (D : DeltaStructure p B) (hD : D.IsPerfect) (d : A)
    (θ : A →+* R) (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {d})
    (w : A →+* B) (hw : Function.Surjective w) (hd : D.IsDistinguished (w d))
    (I : Ideal R) (hI : I ≤ (RingHom.ker w).map θ)
    (qR : R →+* C) (hqR : Function.Surjective qR)
    (hExtend : ∀ (T : Type u) [CommRing T], IsIntegralPerfectoid T p →
      ∀ i : R →+* T, I ≤ RingHom.ker i → ∃ c : C →+* T, c.comp qR = i)
    (β : B →+* C) (hβ : β.comp w = qR.comp θ) :
    letI := pdCompletionCommRing B p (w d)
    ∃ e : C ≃+* PDCompletionH0 B p (w d) ⧸ Ideal.span {pdCompletionUnit B p (w d) (w d)},
      e.toRingHom.comp qR =
        θ.liftOfSurjective hθ ⟨(Ideal.Quotient.mk _).comp
          ((pdCompletionUnit B p (w d)).comp w), by
            rw [hker, Ideal.span_singleton_le_iff_mem]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩ := by
  let := pdCompletionCommRing B p (w d)
  let H := PDCompletionH0 B p (w d)
  let j := pdCompletionUnit B p (w d)
  let U := H ⧸ Ideal.span {j (w d)}
  let qU := Ideal.Quotient.mk (Ideal.span {j (w d)})
  let := perfectDeltaPDPrism_quotient_isAdicComplete D hD (w d) hd
  let i : R →+* U := θ.liftOfSurjective hθ ⟨qU.comp (j.comp w), by
    rw [hker, Ideal.span_singleton_le_iff_mem]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩
  have hiθ : i.comp θ = qU.comp (j.comp w) := θ.liftOfSurjective_comp hθ _
  have hiI : I ≤ RingHom.ker i := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := Ideal.mem_image_of_mem_map_of_surjective θ hθ (hI hr)
    change i r = 0
    rw [← hxr]
    have hh : i (θ x) = qU (j (w x)) := RingHom.congr_fun hiθ x
    rw [hh, show w x = 0 from hx, map_zero, map_zero]
  have hU : IsIntegralPerfectoid U p :=
    (perfectDeltaPDPrism D hD (w d) hd).quotient_isIntegralPerfectoid
      (perfectDeltaPDPrism_isPerfect D hD (w d) hd)
  obtain ⟨c, hcR⟩ := hExtend U hU i hiI
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
    obtain ⟨r, rfl⟩ := hqR x
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
