module

public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionSum
public import SerrePositivity.BhattScholze.DeltaPDivisionTwoStep

/-! # 二入力の同時raw p除算包のp正則性

二段除算との標準同型を通じてp正則性を移す。ghost単射は各段で仮定する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y₀ y₁ : A)
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y₀
local notation "a₁" => fun _ : σ ↦ D.frobeniusLift y₁
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "S" => DeltaAdjoinDivision D (p : A) (Sum.elim a₀ a₁)

/-- 二つのFrobenius入力の同時raw p除算包は、具体的な逐次正則性の仮定の下でp正則。 -/
theorem deltaPDivisionPair_p_mul_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B₀) σ) → ℕ → RelativeFreeDeltaRing (R := B₀) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hy₀ : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y₀))
    (hy₁ : IsSMulRegular (A ⧸ Ideal.span {(p : A), y₀ ^ p})
      (Ideal.Quotient.mk (Ideal.span {(p : A), y₀ ^ p}) y₁)) :
    Function.Injective (fun s : S ↦ (p : S) * s) := by
  let e := deltaAdjoinDivisionSumEquiv D (p : A) a₀ a₁
  have hφ : (fun _ : σ ↦ j₀ (D.frobeniusLift y₁)) =
      (fun _ : σ ↦ (E₀).frobeniusLift (j₀ y₁)) := by
    funext s
    exact (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a₀).map_frobeniusLift y₁
  have hpT : Function.Injective (fun t : DeltaAdjoinDivision E₀ (j₀ (p : A))
      (fun _ : σ ↦ j₀ (D.frobeniusLift y₁)) ↦
      (p : DeltaAdjoinDivision E₀ (j₀ (p : A)) (fun _ : σ ↦ j₀ (D.frobeniusLift y₁))) * t) := by
    rw [map_natCast, hφ]
    exact deltaPDivisionTwoStep_p_mul_injective (σ := σ) D y₀ y₁ hpA hg₀ hg₁ w hw hy₀ hy₁
  intro s t hst
  apply e.injective
  apply hpT
  simpa only [map_mul, map_natCast] using congrArg e hst

/-- 同じ仮定で、二つのp乗入力の同時raw p除算包もp正則。 -/
theorem deltaPDivisionPairPower_p_mul_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B₀) σ) → ℕ → RelativeFreeDeltaRing (R := B₀) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hy₀ : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y₀))
    (hy₁ : IsSMulRegular (A ⧸ Ideal.span {(p : A), y₀ ^ p})
      (Ideal.Quotient.mk (Ideal.span {(p : A), y₀ ^ p}) y₁)) :
    Function.Injective (fun s : DeltaAdjoinDivision D (p : A)
      (fun t : σ ⊕ σ ↦ (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) t) ^ p) ↦
      (p : DeltaAdjoinDivision D (p : A)
        (fun t : σ ⊕ σ ↦ (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) t) ^ p)) * s) := by
  let e := deltaPDivisionFrobeniusShiftEquiv D
    (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁))
  have hφ : (fun s : σ ⊕ σ ↦ D.frobeniusLift
      (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) s)) = Sum.elim a₀ a₁ := by
    funext s
    cases s <;> rfl
  have hpφ : Function.Injective (fun s : DeltaAdjoinDivision D (p : A)
      (fun t : σ ⊕ σ ↦ D.frobeniusLift
        (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) t)) ↦
      (p : DeltaAdjoinDivision D (p : A) (fun t : σ ⊕ σ ↦ D.frobeniusLift
        (Sum.elim (fun _ : σ ↦ y₀) (fun _ : σ ↦ y₁) t))) * s) := by
    rw [hφ]
    exact deltaPDivisionPair_p_mul_injective (σ := σ) D y₀ y₁ hpA hg₀ hg₁ w hw hy₀ hy₁
  intro s t hst
  apply e.symm.injective
  apply hpφ
  simpa only [map_mul, map_natCast] using congrArg e.symm hst

end SerrePositivity.BhattScholze
