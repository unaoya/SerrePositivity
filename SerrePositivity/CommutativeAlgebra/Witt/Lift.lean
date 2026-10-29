module

public import Mathlib.RingTheory.WittVector.TeichmullerSeries
public import Mathlib.LinearAlgebra.SModEq.Pow
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Witt ベクトルの普遍性と strict p 環

## 概要

`k` を標数 `p` の完全環、`A` を `p` 進完備な環とする。
- 任意の `s : k →+* A/p` に対し、`W(k) → A` で mod `p` が `s ∘ (第 0 係数)` となるものがただ一つある
  （`wittResidueLift`、`existsUnique_wittResidueLift`、零環も含む版は
  `existsUnique_wittResidueLift_of_complete`）。一意性は `A` が `p` 進分離なら成り立つ（`wittLift_unique`）。
- strict p 環の復元：`A/p` が完全で `p` 倍が単射なら `W(A/p) ≃+* A`（`strictPRecoveryEquiv`）。
  `W(k) → A` の単射・全射の判定（`wittLift_injective`、`wittLift_surjective`）を含む。

## 方針

存在：`s` を `Perfection.lift` で `A` の tilt への写像に持ち上げ、Mathlib の Fontaine θ と合成する。
一意性：二つの写像は Teichmüller 元で一致し（各 `p^n` 進近似で `p^n` 乗根をとる）、
Mathlib の `WittVector.eq_of_apply_teichmuller_eq` を `p` 進分離性で極限へ移す。
strict p 環：単射性・全射性を mod `p` と `p` 進完備性から示し、`p` が単元（零環）の場合を分ける。

## 規約

復元同型は `p` が単元かどうかで場合分けした def として与え、`.choose` は使わない。
Mathlib の `WittVector/` と `Perfectoid/FontaineTheta` を延長する内容で、Mathlib への提出候補
（mathlib-upstream の G7）。

## 使われ方

完全 δ 環と perfect prism（BhattScholze の `PerfectDelta`、`PerfectPrismHomLift`、`WittPushout` など）、
Cohen 環の係数写像（`Witt/CohenRing`）。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity

section Uniqueness

variable {p : ℕ} [Fact p.Prime] {k A : Type*} [CommRing k] [CharP k p]
    [PerfectRing k p] [CommRing A]

/-- 同じmod p写像を持つWitt写像はTeichmüller元で一致する。 -/
theorem wittLift_teichmuller_eq [IsHausdorff (Ideal.span {(p : A)}) A]
    (f g : WittVector p k →+* A)
    (h : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f =
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp g) (x : k) :
    f (WittVector.teichmuller p x) = g (WittVector.teichmuller p x) := by
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A)})).mpr
  intro n
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hsurj : Function.Surjective (fun y : k ↦ y ^ p ^ n) := by
    have hs := (PerfectRing.bijective_frobenius (R := k) (p := p)).surjective.iterate n
    change Function.Surjective (frobenius k p)^[n] at hs
    intro a
    obtain ⟨y, hy⟩ := hs a
    exact ⟨y, by simpa only [iterate_frobenius] using hy⟩
  obtain ⟨y, rfl⟩ := hsurj x
  have hmod : f (WittVector.teichmuller p y) ≡ g (WittVector.teichmuller p y)
      [SMOD Ideal.span {(p : A)}] := by
    exact SModEq.idealQuotientMk.mpr (RingHom.congr_fun h _)
  have he := hmod.pow_pow_add_one
    (Ideal.mem_span_singleton_self (p : A)) n
  have ht := he.mono (Ideal.pow_le_pow_right (Nat.le_succ n))
  simpa only [map_pow] using ht

/-- 同じmod p写像を持つ任意の二つの環準同型は一致する。連続性を仮定しない。 -/
theorem wittLift_unique [IsHausdorff (Ideal.span {(p : A)}) A]
    (f g : WittVector p k →+* A)
    (h : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f =
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp g) : f = g := by
  ext x
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A)})).mpr
  intro n
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  apply SModEq.idealQuotientMk.mpr
  have he : (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ n)).comp f =
      (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ n)).comp g := by
    apply WittVector.eq_of_apply_teichmuller_eq
    · refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : A)) n)
    · intro y
      simp only [RingHom.comp_apply, wittLift_teichmuller_eq f g h y]
  exact RingHom.congr_fun he x

end Uniqueness

section Construction

set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]
    [Fact (¬ IsUnit (p : A))] [IsAdicComplete (Ideal.span {(p : A)}) A]
    (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- 剰余写像をPerfectionへ持ち上げ、Fontaine θと合成する。 -/
def wittResidueLift (s : k →+* ModP A p) : WittVector p k →+* A :=
  let t : k →+* PreTilt A p := Perfection.lift p k (ModP A p) s
  (WittVector.fontaineTheta A p).comp (WittVector.map t)

/-- Witt持上げのmod p図式。 -/
theorem wittResidueLift_mod_p (s : k →+* ModP A p) :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp (wittResidueLift p A k s) =
      s.comp WittVector.constantCoeff := by
  ext x
  let t : k →+* PreTilt A p := Perfection.lift p k (ModP A p) s
  have hm := WittVector.mk_fontaineTheta (WittVector.map t x)
  rw [WittVector.map_coeff] at hm
  exact hm

/-- 指定した剰余写像のWitt持上げは一意に存在する。 -/
theorem existsUnique_wittResidueLift (s : k →+* ModP A p) :
    ∃! f : WittVector p k →+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f = s.comp WittVector.constantCoeff := by
  refine ⟨wittResidueLift p A k s, wittResidueLift_mod_p p A k s, ?_⟩
  intro f hf
  exact wittLift_unique f (wittResidueLift p A k s)
    (hf.trans (wittResidueLift_mod_p p A k s).symm)

end Construction

section StrictP

set_option backward.isDefEq.respectTransparency false
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

open Classical in
/-- strict p 環の Witt 復元同型。`p` が単元なら零環どうしの同型、そうでなければ構成した同型。 -/
def strictPRecoveryEquiv [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    WittVector p (ModP A p) ≃+* A :=
  if hu : IsUnit (p : A) then
    haveI := subsingleton_of_isUnit_natCast_of_isHausdorff p A hu
    strictPRecoveryEquivOfSubsingleton p A
  else
    haveI : Fact (¬ IsUnit (p : A)) := ⟨hu⟩
    strictPRecoveryEquivOfNonunit p A hp

/-- 復元同型の mod `p` は第 0 係数。零環を含む。 -/
theorem strictPRecoveryEquiv_mod_p [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp
      (strictPRecoveryEquiv p A hp).toRingHom = WittVector.constantCoeff := by
  by_cases hu : IsUnit (p : A)
  · have := subsingleton_of_isUnit_natCast_of_isHausdorff p A hu
    ext x
    exact Subsingleton.elim _ _
  · have : Fact (¬ IsUnit (p : A)) := ⟨hu⟩
    simp only [strictPRecoveryEquiv, hu, ↓reduceDIte]
    exact strictPRecoveryEquivOfNonunit_mod_p p A hp

/-- 復元同型の存在と mod `p` の可換性（`strictPRecoveryEquiv` の系）。 -/
theorem exists_strictPRecoveryEquiv [IsAdicComplete (Ideal.span {(p : A)}) A]
    [PerfectRing (ModP A p) p]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    ∃ e : WittVector p (ModP A p) ≃+* A,
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp e.toRingHom = WittVector.constantCoeff :=
  ⟨strictPRecoveryEquiv p A hp, strictPRecoveryEquiv_mod_p p A hp⟩

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

end StrictP

end SerrePositivity
