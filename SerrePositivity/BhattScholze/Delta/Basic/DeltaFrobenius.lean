module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaIdentities

/-! # p正則な環のFrobenius持上げとδ構造

BS著者版Remark 2.2。mod pでFrobeniusと一致する環自己準同型から
δ構造を構成し、一意性を証明する。pねじれのある環への逆向きは主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p正則な環では、φ(x)-x^pがpで割り切れる自己準同型φは一意なδ構造を定める。
p倍の消去でδの恒等式を証明し、W₂切断を再構成する（BS Remark 2.2）。 -/
theorem existsUnique_of_frobeniusLift
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) (φ : A →+* A)
    (hφ : ∀ x, (p : A) ∣ φ x - x ^ p) :
    ∃! D : DeltaStructure p A, D.frobeniusLift = φ := by
  let δ : A → A := fun x ↦ Classical.choose (hφ x)
  have hδ (x : A) : φ x = x ^ p + (p : A) * δ x := by
    have h := Classical.choose_spec (hφ x)
    change φ x - x ^ p = (p : A) * δ x at h
    linear_combination h
  have h0 : δ 0 = 0 := by
    apply hp
    have h := hδ 0
    simpa only [map_zero, zero_pow (Fact.out : p.Prime).ne_zero, zero_add, mul_zero]
      using h.symm
  have h1 : δ 1 = 0 := by
    apply hp
    have h := hδ 1
    simp only [map_one, one_pow] at h
    linear_combination -h
  have hadd (x y : A) : δ (x + y) = δ x + δ y +
      (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
    apply hp
    have h := φ.map_add x y
    rw [hδ (x + y), hδ x, hδ y] at h
    have hc := (WittVector.ghostComponent 1).map_add
      (WittVector.teichmuller p x) (WittVector.teichmuller p y)
    simp only [witt_ghostComponent_one, WittVector.add_coeff_zero,
      WittVector.teichmuller_coeff_zero,
      WittVector.teichmuller_coeff_pos p _ 1 (by decide), mul_zero, zero_add] at hc
    linear_combination h - hc
  have hmul (x y : A) : δ (x * y) = x ^ p * δ y + δ x * y ^ p +
      (p : A) * δ x * δ y := by
    apply hp
    have h := φ.map_mul x y
    rw [hδ (x * y), hδ x, hδ y, mul_pow] at h
    linear_combination h
  let D := ofFunction δ h0 h1 hadd hmul
  have hD : D.frobeniusLift = φ := by
    ext x
    exact (D.frobeniusLift_apply x).trans (hδ x).symm
  exact ⟨D, hD, fun E hE ↦ eq_of_frobeniusLift_eq hp (hE.trans hD.symm)⟩

/-- mod pでFrobeniusとなる自己準同型は、p正則な環に一意なδ構造を与える。
商上の一致をpによる可除性へ移し、存在定理を適用する。 -/
theorem existsUnique_of_mod_p
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) (φ : A →+* A)
    (hφ : ∀ x, Ideal.Quotient.mk (Ideal.span {(p : A)}) (φ x) =
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) x) ^ p) :
    ∃! D : DeltaStructure p A, D.frobeniusLift = φ := by
  apply existsUnique_of_frobeniusLift hp φ
  intro x
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_pow, hφ x, sub_self]

end SerrePositivity.BhattScholze.DeltaStructure
