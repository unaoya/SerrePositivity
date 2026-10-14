module

public import SerrePositivity.BhattScholze.PerfectDeltaModP
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # 完全δ環のFrobenius同型とδ

p正則なδ環のFrobeniusはδ射であり、完全δ環では逆Frobeniusもδ射となる。
完全化に使うFrobeniusの反復図式をδ環の図式として扱うための補題。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p正則なδ環のFrobenius持上げはδと可換。
φ自身との可換性から、p正則な終域におけるδ射の判定を使う。 -/
theorem isDeltaHom_frobeniusLift (D : DeltaStructure p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) : D.IsDeltaHom D D.frobeniusLift :=
  isDeltaHom_of_map_frobeniusLift D.frobeniusLift hp (fun _ ↦ rfl)

/-- δ射である環同型の逆もδ射。完全δ環の逆Frobeniusに使う。 -/
theorem IsDeltaHom.symm {B : Type v} [CommRing B] {D : DeltaStructure p A}
    {E : DeltaStructure p B} {e : A ≃+* B} (he : D.IsDeltaHom E e.toRingHom) :
    E.IsDeltaHom D e.symm.toRingHom := by
  intro x
  apply e.injective
  change e (e.symm (E.delta x)) = e (D.delta (e.symm x))
  have h := he (e.symm x)
  change e (D.delta (e.symm x)) = E.delta (e (e.symm x)) at h
  simpa only [e.apply_symm_apply] using h.symm

/-- 完全δ環のFrobeniusを環同型として束ねる。 -/
def frobeniusEquiv (D : DeltaStructure p A) (hD : D.IsPerfect) : A ≃+* A :=
  RingEquiv.ofBijective D.frobeniusLift hD

/-- 完全δ環のFrobenius同型はδ射。前段で証明したp正則性を使う。 -/
theorem frobeniusEquiv_isDeltaHom (D : DeltaStructure p A) (hD : D.IsPerfect) :
    D.IsDeltaHom D (D.frobeniusEquiv hD).toRingHom :=
  D.isDeltaHom_frobeniusLift hD.p_mul_injective

/-- 完全δ環の逆Frobeniusもδ射。完全化図式とWitt比較の自然性に用いる。 -/
theorem frobeniusEquiv_symm_isDeltaHom (D : DeltaStructure p A) (hD : D.IsPerfect) :
    D.IsDeltaHom D (D.frobeniusEquiv hD).symm.toRingHom :=
  (D.frobeniusEquiv_isDeltaHom hD).symm

/-- 完全δ環のFrobeniusは各mod p^n商の環自己同型を誘導する。
φ(p)=pから(p)^nの像が同じイデアルであることを使う。 -/
def frobeniusModPowEquiv (D : DeltaStructure p A) (hD : D.IsPerfect) (n : ℕ) :
    A ⧸ (Ideal.span {(p : A)}) ^ n ≃+* A ⧸ (Ideal.span {(p : A)}) ^ n :=
  Ideal.quotientEquiv _ _ (D.frobeniusEquiv hD) (by
    simp only [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast])

/-- mod p^n Frobenius同型は代表元上で元環のφを適用する。 -/
@[simp] theorem frobeniusModPowEquiv_mk (D : DeltaStructure p A) (hD : D.IsPerfect)
    (n : ℕ) (x : A) :
    D.frobeniusModPowEquiv hD n (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ n) x) =
      Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ n) (D.frobeniusLift x) := rfl

/-- mod p^n Frobenius同型は商の遷移写像と両立する。
完備化でFrobeniusとその逆を比較するための具体的な可換図式。 -/
theorem frobeniusModPowEquiv_compatible (D : DeltaStructure p A) (hD : D.IsPerfect)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : A)}) hmn).comp
        (D.frobeniusModPowEquiv hD n).toRingHom =
      (D.frobeniusModPowEquiv hD m).toRingHom.comp
        (Ideal.Quotient.factorPow (Ideal.span {(p : A)}) hmn) := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end SerrePositivity.BhattScholze.DeltaStructure
