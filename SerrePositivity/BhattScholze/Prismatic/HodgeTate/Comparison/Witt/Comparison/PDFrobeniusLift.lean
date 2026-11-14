module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.CompletedPDEnvelope
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase

/-!
# 分冪包上の Frobenius の持ち上げ

## 概要
分冪基底の Frobenius が分冪イデアルを p へ送るとき、
多項式枠の完備分冪包に Frobenius を延長する。

## 方針
標的の (p) の標準分冪に対し、変数の p 乗を指定して包の普遍性を使う。
mod p では分冪イデアルが p 乗で消えるため、延長は通常の Frobenius と一致する。

## 規約
標的環の p 正則性は明示する。δ 構造はその正則性を用いて復元する。

## 使われ方
BS 著者版 Lemma 2.38 と Theorem 6.4 の大きい分冪模型。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

private def frobeniusOfPrimeZero {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    (hp : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow _
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' x y := by rw [add_pow_prime_eq' (Fact.out : p.Prime), hp, zero_mul, add_zero]

private theorem factorial_regular {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    (hp : Function.Injective (fun x : R => (p : R) * x))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : R)) (n : ℕ) :
    Function.Injective (fun x : R => (n.factorial : R) * x) := by
  let L := Localization.Away (p : R)
  let f := algebraMap R L
  let : Algebra ℚ L := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  intro x y h
  apply away_injective_of_prime p hp
  apply (IsUnit.natCast_factorial_of_algebra ℚ n (A := L)).mul_left_cancel
  simpa only [map_mul, map_natCast] using congrArg f h

private theorem isDPMorphism_of_ideal_le {p : ℕ} [Fact p.Prime]
    {A D : Type u} [CommRing A] [CommRing D] {I : Ideal A} {J : Ideal D}
    (γ : DividedPowers I) (δ : DividedPowers J) (f : A →+* D) (hJ : I.map f ≤ J)
    (hp : Function.Injective (fun x : D => (p : D) * x))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : D)) :
    γ.IsDPMorphism δ f := by
  refine ⟨hJ, fun {n} x hx => ?_⟩
  apply factorial_regular hp hlocal n
  change (n.factorial : D) * δ.dpow n (f x) = (n.factorial : D) * f (γ.dpow n x)
  rw [δ.factorial_mul_dpow_eq_pow (hJ (Ideal.mem_map_of_mem _ hx))]
  simpa only [map_mul, map_natCast, map_pow] using
    (congrArg f (γ.factorial_mul_dpow_eq_pow (n := n) hx)).symm

private def FrobeniusTarget (R : Type u) := R

private instance (R : Type u) [CommRing R] : CommRing (FrobeniusTarget R) :=
  inferInstanceAs (CommRing R)

section Envelope

variable {p : ℕ} [Fact p.Prime] {k σ : Type u} [CommRing k]
variable (Dk : DeltaStructure p k) {J : Ideal k} (γ : DividedPowers J)
variable {K : Ideal (MvPolynomial σ k)} (E : CompletedPDEnvelopeData p γ K)

local notation "D" => E.carrier
local notation "I" => E.ideal
local notation "P" => Ideal.span {(p : D)}
local notation "q" => Ideal.Quotient.mk P

variable (hreg : Function.Injective (fun x : E.carrier => (p : E.carrier) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : k))
variable (hφ : J.map Dk.frobeniusLift ≤ Ideal.span {(p : k)})

omit [Fact p.Prime] in
include hlocal in
private theorem local_carrier (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : D) := by
  simpa only [map_natCast] using (hlocal m hm).map (algebraMap k D)

private def scalarFrobenius : k →+* D := (algebraMap k D).comp Dk.frobeniusLift

include hφ in
private theorem scalarFrobenius_map_le : J.map (scalarFrobenius Dk γ E) ≤ P := by
  rw [scalarFrobenius, ← Ideal.map_map]
  apply (Ideal.map_mono hφ).trans
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

private def frobeniusPolynomial : MvPolynomial σ k →+* D :=
  MvPolynomial.eval₂Hom (scalarFrobenius Dk γ E) (fun i => E.unit (MvPolynomial.X i) ^ p)

omit [Fact p.Prime] in
private theorem quotient_prime_zero : (p : D ⧸ P) = 0 := by
  rw [← map_natCast q]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

private theorem quotient_frobeniusPolynomial :
    (q).comp (frobeniusPolynomial Dk γ E) =
      (frobeniusOfPrimeZero (quotient_prime_zero γ E)).comp ((q).comp E.unit.toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change q (frobeniusPolynomial Dk γ E (MvPolynomial.C a)) = (q (E.unit (MvPolynomial.C a))) ^ p
    rw [frobeniusPolynomial, MvPolynomial.eval₂Hom_C]
    change ((q).comp (algebraMap k D)) (Dk.frobeniusLift a) =
      (q (E.unit (algebraMap k (MvPolynomial σ k) a))) ^ p
    rw [E.unit.commutes]
    exact Dk.map_frobeniusLift_of_map_p_eq_zero _ (by rw [map_natCast, quotient_prime_zero γ E]) a
  · intro i
    change q (frobeniusPolynomial Dk γ E (MvPolynomial.X i)) = (q (E.unit (MvPolynomial.X i))) ^ p
    rw [frobeniusPolynomial, MvPolynomial.eval₂Hom_X', map_pow]

private theorem frobenius_ideal_le_ker :
    I ≤ RingHom.ker ((frobeniusOfPrimeZero (quotient_prime_zero γ E)).comp q) := by
  intro x hx
  change (q x) ^ p = 0
  rw [← map_pow, ← E.dividedPowers.factorial_mul_dpow_eq_pow (n := p) hx]
  have hfac : (p.factorial : D ⧸ P) = 0 := by
    obtain ⟨m, hm⟩ := Nat.dvd_factorial (Fact.out : p.Prime).pos (Nat.le_refl p)
    rw [hm, Nat.cast_mul, quotient_prime_zero γ E, zero_mul]
  rw [map_mul, map_natCast, hfac, zero_mul]

private theorem frobeniusPolynomial_map_le : K.map (frobeniusPolynomial Dk γ E) ≤ P := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change frobeniusPolynomial Dk γ E x ∈ P
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have H := RingHom.congr_fun (quotient_frobeniusPolynomial Dk γ E) x
  exact H.trans (RingHom.mem_ker.mp
    (frobenius_ideal_le_ker γ E (E.isEnvelope.map_le (Ideal.mem_map_of_mem E.unit hx))))

include hφ in
private theorem exists_frobeniusLift :
    ∃ F : D →+* D,
      E.dividedPowers.IsDPMorphism (residuePdStructure p hreg (local_carrier γ E hlocal)) F ∧
      F.comp E.unit.toRingHom = frobeniusPolynomial Dk γ E := by
  let T := FrobeniusTarget D
  let : Algebra k T := (show k →+* T from scalarFrobenius Dk γ E).toAlgebra
  let g : MvPolynomial σ k →ₐ[k] T :=
    ⟨frobeniusPolynomial Dk γ E, MvPolynomial.eval₂Hom_C _ _⟩
  let P' : Ideal T := P
  let ε : DividedPowers P' := residuePdStructure p hreg (local_carrier γ E hlocal)
  have hI : K.map g ≤ P' := frobeniusPolynomial_map_le Dk γ E
  have hd : γ.IsDPMorphism ε (algebraMap k T) :=
    isDPMorphism_of_ideal_le γ ε (scalarFrobenius Dk γ E)
      (scalarFrobenius_map_le Dk γ E hφ) hreg (local_carrier γ E hlocal)
  have hc : IsAdicComplete (Ideal.span {(p : T)}) T := E.isEnvelope.complete
  obtain ⟨f, hf, _⟩ := E.isEnvelope.lift ε hc g hI hd
  exact ⟨f.toRingHom, hf.1, congrArg AlgHom.toRingHom hf.2⟩

include hreg hlocal hφ in
/-- p 正則な完備分冪包の δ 構造。枠の変数の δ は零になる。 -/
theorem exists_deltaStructure_of_pdPolynomial :
    ∃ Δ : DeltaStructure p D, Dk.IsDeltaHom Δ (algebraMap k D) ∧
      (∀ i : σ, Δ.delta (E.unit (MvPolynomial.X i)) = 0) ∧
      E.dividedPowers.IsDPMorphism (residuePdStructure p hreg (fun m hm => by
        simpa only [map_natCast] using (hlocal m hm).map (algebraMap k D))) Δ.frobeniusLift := by
  let ε := residuePdStructure p hreg (local_carrier γ E hlocal)
  obtain ⟨F, hFdp, hF⟩ := exists_frobeniusLift Dk γ E hreg hlocal hφ
  have hFb : F.comp (algebraMap k D) = scalarFrobenius Dk γ E := by
    apply RingHom.ext
    intro a
    have H := RingHom.congr_fun hF (MvPolynomial.C a)
    change F (E.unit (algebraMap k (MvPolynomial σ k) a)) = _ at H
    rw [E.unit.commutes, frobeniusPolynomial, MvPolynomial.eval₂Hom_C] at H
    exact H
  let Q := D ⧸ P
  let b := (q).comp (scalarFrobenius Dk γ E)
  let : Algebra k Q := b.toAlgebra
  let F₀ : @AlgHom k D Q _ _ _ E.algebra inferInstance :=
    ⟨(q).comp F, fun a => congrArg q (RingHom.congr_fun hFb a)⟩
  let F₁ : @AlgHom k D Q _ _ _ E.algebra inferInstance :=
    ⟨(frobeniusOfPrimeZero (quotient_prime_zero γ E)).comp q, fun a =>
      (Dk.map_frobeniusLift_of_map_p_eq_zero ((q).comp (algebraMap k D))
        (by rw [map_natCast, quotient_prime_zero γ E]) a).symm⟩
  have h₀ : I ≤ RingHom.ker F₀.toRingHom := by
    intro x hx
    change q (F x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hFdp.ideal_comp (Ideal.mem_map_of_mem _ hx))
  have h₁ : I ≤ RingHom.ker F₁.toRingHom := frobenius_ideal_le_ker γ E
  have hQ : IsAdicComplete (Ideal.span {(p : Q)}) Q :=
    isAdicComplete_of_natCast_zero (quotient_prime_zero γ E)
  have hE : F₀ = F₁ := by
    apply E.isEnvelope.hom_ext hQ (isDPMorphismToBot E.dividedPowers _ h₀)
      (isDPMorphismToBot E.dividedPowers _ h₁)
    apply AlgHom.toRingHom_injective
    change ((q).comp F).comp E.unit.toRingHom =
      ((frobeniusOfPrimeZero (quotient_prime_zero γ E)).comp q).comp E.unit.toRingHom
    rw [RingHom.comp_assoc, hF, quotient_frobeniusPolynomial, RingHom.comp_assoc]
  have hmod (x : D) : q (F x) = (q x) ^ p := DFunLike.congr_fun hE x
  obtain ⟨Δ, hΔ, _⟩ := DeltaStructure.existsUnique_of_mod_p hreg F hmod
  refine ⟨Δ, ?_, ?_, ?_⟩
  · apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _ hreg
    intro a
    rw [hΔ]
    exact (RingHom.congr_fun hFb a).symm
  · intro i
    apply hreg
    have H := RingHom.congr_fun hF (MvPolynomial.X i)
    change F (E.unit (MvPolynomial.X i)) = _ at H
    rw [frobeniusPolynomial, MvPolynomial.eval₂Hom_X'] at H
    have H' := Δ.frobeniusLift_apply (E.unit (MvPolynomial.X i))
    rw [hΔ, H] at H'
    exact (add_left_cancel (H'.symm.trans (add_zero _).symm)).trans (mul_zero _).symm
  · rw [hΔ]
    exact hFdp

end Envelope

end SerrePositivity.BhattScholze.Prismatic
