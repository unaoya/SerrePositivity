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
  apply SModEq.sub_mem.mpr
  simpa only [sub_zero] using Ideal.mem_span_singleton.mpr (hpow n x hx)

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

section Nonunit
variable [Fact (¬ IsUnit (p : A))] [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]

/-- 非零strict p環の標準Witt復元写像。 -/
def strictPRecoveryHom : WittVector p (ModP A p) →+* A :=
  wittResidueLift p A (ModP A p) (RingHom.id _)

/-- 復元写像の剰余図式。 -/
theorem strictPRecoveryHom_mod_p :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp (strictPRecoveryHom p A) =
      WittVector.constantCoeff := by
  simpa only [strictPRecoveryHom, RingHom.id_comp] using
    wittResidueLift_mod_p p A (ModP A p) (RingHom.id _)

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

end Nonunit

omit [Fact p.Prime] in
/-- pが単元でp進分離な環は零環。 -/
theorem subsingleton_of_isUnit_natCast_of_isHausdorff
    [IsHausdorff (Ideal.span {(p : A)}) A] (hu : IsUnit (p : A)) : Subsingleton A := by
  apply subsingleton_of_forall_eq 0
  intro x
  apply IsHausdorff.haus' (I := Ideal.span {(p : A)})
  intro n
  apply SModEq.sub_mem.mpr
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  rw [Ideal.span_singleton_eq_top.mpr (hu.pow n)]
  exact Submodule.mem_top

/-- 零環のWitt復元。剰余環にCharP pを要求しない。 -/
def strictPRecoveryEquivOfSubsingleton [Subsingleton A] :
    WittVector p (ModP A p) ≃+* A := by
  letI : Subsingleton (WittVector p (ModP A p)) := by
    constructor
    intro x y
    ext n
    exact Subsingleton.elim _ _
  exact
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _
      map_mul' := fun _ _ ↦ Subsingleton.elim _ _
      map_add' := fun _ _ ↦ Subsingleton.elim _ _ }

/-- F4の要求する一般環のWitt復元の存在と標準商写像の可換性。 -/
theorem exists_strictPRecoveryEquiv [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    ∃ e : WittVector p (ModP A p) ≃+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp e.toRingHom = WittVector.constantCoeff := by
  classical
  by_cases hu : IsUnit (p : A)
  · have := subsingleton_of_isUnit_natCast_of_isHausdorff p A hu
    refine ⟨strictPRecoveryEquivOfSubsingleton p A, ?_⟩
    ext x
    exact Subsingleton.elim _ _
  · have : Fact (¬ IsUnit (p : A)) := ⟨hu⟩
    exact ⟨strictPRecoveryEquivOfNonunit p A hp, strictPRecoveryEquivOfNonunit_mod_p p A hp⟩

/-- 零環を含む標準Witt復元環同型。 -/
def strictPRecoveryEquiv [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    WittVector p (ModP A p) ≃+* A := (exists_strictPRecoveryEquiv p A hp).choose

/-- 公開した復元同型の標準剰余図式。 -/
theorem strictPRecoveryEquiv_mod_p [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp
      (strictPRecoveryEquiv p A hp).toRingHom = WittVector.constantCoeff :=
  (exists_strictPRecoveryEquiv p A hp).choose_spec

/-- 同じ標準剰余写像を持つ任意の二つの環準同型の一致。零環を含む。 -/
theorem strictPRecovery_unique [IsHausdorff (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]
    (f g : WittVector p (ModP A p) →+* A)
    (hf : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f = WittVector.constantCoeff)
    (hg : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp g = WittVector.constantCoeff) :
    f = g := by
  classical
  by_cases hu : IsUnit (p : A)
  · have := subsingleton_of_isUnit_natCast_of_isHausdorff p A hu
    ext x
    exact Subsingleton.elim _ _
  · have : Fact (¬ IsUnit (p : A)) := ⟨hu⟩
    exact wittLift_unique f g (hf.trans hg.symm)

/-- 任意のp進完備環への一般Witt持上げ。零環も含み、p正則性を要しない。 -/
theorem existsUnique_wittResidueLift_of_complete
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
    (s : k →+* ModP A p) :
    ∃! f : WittVector p k →+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f = s.comp WittVector.constantCoeff := by
  classical
  by_cases hu : IsUnit (p : A)
  · have := subsingleton_of_isUnit_natCast_of_isHausdorff p A hu
    let f : WittVector p k →+* A :=
      { toFun := fun _ ↦ 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
    refine ⟨f, ?_, ?_⟩
    · ext x
      exact Subsingleton.elim _ _
    · intro g _
      ext x
      exact Subsingleton.elim _ _
  · have : Fact (¬ IsUnit (p : A)) := ⟨hu⟩
    exact existsUnique_wittResidueLift p A k s

end SerrePositivity
