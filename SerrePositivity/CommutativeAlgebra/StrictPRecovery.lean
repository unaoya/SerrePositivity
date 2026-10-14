module

public import SerrePositivity.CommutativeAlgebra.WittLiftConstruction
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # strict p環のWitt復元 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]

/-- 完全標数p環のWitt写像がmod pで単射なら、p正則な終域への写像も単射。 -/
theorem wittLift_injective {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
    (f : WittVector p k →+* A) (s : k →+* ModP A p) (hs : Function.Injective s)
    (hf : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f = s.comp WittVector.constantCoeff)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) : Function.Injective f := by
  have hdiv (x : WittVector p k) (hx : f x = 0) : ∃ y, (p : WittVector p k) * y = x ∧ f y = 0 := by
    have hc : x.coeff 0 = 0 := by
      apply hs
      simpa only [RingHom.comp_apply, WittVector.constantCoeff_apply, hx, map_zero] using
        (RingHom.congr_fun hf x).symm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp
      ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).mpr hc)
    refine ⟨y, hy.symm, ?_⟩
    apply hp
    simpa only [mul_zero, ← map_natCast f p, ← map_mul, ← hy] using hx
  have hpow (n : ℕ) (x : WittVector p k) (hx : f x = 0) :
      (p : WittVector p k) ^ n ∣ x := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      obtain ⟨y, hy, hfy⟩ := hdiv x hx
      obtain ⟨z, hz⟩ := ih y hfy
      refine ⟨z, ?_⟩
      rw [← hy, hz, pow_succ']
      ring
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  apply IsHausdorff.haus' (I := Ideal.span {(p : WittVector p k)})
  intro n
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact SModEq.sub_mem.mpr (by simpa only [sub_zero] using Ideal.mem_span_singleton.mpr (hpow n x hx))

/-- Witt持上げがmod pで全射なら、p進完備な始域と分離な終域から全射。 -/
theorem wittLift_surjective [IsHausdorff (Ideal.span {(p : A)}) A]
    {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
    (f : WittVector p k →+* A) (s : k →+* ModP A p) (hs : Function.Surjective s)
    (hf : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f = s.comp WittVector.constantCoeff) :
    Function.Surjective f := by
  have hmap : (Ideal.span {(p : WittVector p k)}).map f = Ideal.span {(p : A)} := by
    simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  have hhaus : IsHausdorff ((Ideal.span {(p : WittVector p k)}).map f) A := by
    rw [hmap]
    infer_instance
  let := hhaus
  apply surjective_of_mk_map_comp_surjective f (I := Ideal.span {(p : WittVector p k)})
  rw [hmap, hf]
  exact hs.comp (WittVector.constantCoeff_surjective p)

variable [Fact (¬ IsUnit (p : A))] [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]

/-- 非零strict p環の標準Witt復元写像。 -/
def strictPRecoveryHom : WittVector p (ModP A p) →+* A :=
  wittResidueLift p A (ModP A p) (RingHom.id _)

/-- 復元写像の剰余図式。 -/
theorem strictPRecoveryHom_mod_p :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp (strictPRecoveryHom p A) =
      WittVector.constantCoeff := by
  simpa only [strictPRecoveryHom, RingHom.id_comp] using wittResidueLift_mod_p p A (ModP A p) (RingHom.id _)

/-- 非零枝のWitt復元環同型。 -/
def strictPRecoveryEquivOfNonunit
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    WittVector p (ModP A p) ≃+* A :=
  RingEquiv.ofBijective (strictPRecoveryHom p A)
    ⟨wittLift_injective p A _ (RingHom.id _) Function.injective_id
      (by simpa using strictPRecoveryHom_mod_p p A) hp,
     wittLift_surjective p A _ (RingHom.id _) Function.surjective_id
      (by simpa using strictPRecoveryHom_mod_p p A)⟩

/-- 非零枝の同型は標準商写像を保つ。 -/
theorem strictPRecoveryEquivOfNonunit_mod_p
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp
      (strictPRecoveryEquivOfNonunit p A hp).toRingHom = WittVector.constantCoeff :=
  strictPRecoveryHom_mod_p p A

end SerrePositivity
