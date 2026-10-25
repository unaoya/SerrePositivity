module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionNextInput
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionRawRegular

/-! # 二段のraw δ p除算包のp正則性

次の入力の係数商での正則性を用いて、一元除算のp正則性を二段へ延ばす。
自由δ環のghost単射は各段で明示的に仮定する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y₀ y₁ : A)
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y₀
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀

omit [Unique σ] in
/-- 指定されたδ(p)の単元は、第一raw除算包でも同じδ(p)を与える。 -/
theorem deltaPDivisionRaw_delta_prime_unit_map
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    ((w.map j₀ : B₀ˣ) : B₀) = (E₀).delta (p : B₀) := by
  change j₀ (w : A) = _
  rw [hw, deltaAdjoinDivisionMap_isDeltaHom D (p : A) a₀ (p : A), map_natCast]

/-- y₁のA/(p,y₀^p)での正則性は第一raw包の実mod p商へ移る。 -/
theorem deltaPDivisionRaw_next_isSMulRegular
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hy₁ : IsSMulRegular (A ⧸ Ideal.span {(p : A), y₀ ^ p})
      (Ideal.Quotient.mk (Ideal.span {(p : A), y₀ ^ p}) y₁)) :
    IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)})
      (Ideal.Quotient.mk (Ideal.span {(p : B₀)}) (j₀ y₁)) := by
  apply deltaPDivisionRawModP_next_isSMulRegular D hpA hg (fun _ : σ ↦ y₀) w hw y₁
  rw [deltaPDivisionFirstBaseIdeal_const_power (p := p) (σ := σ) y₀]
  exact hy₁

/-- 二段の具体的raw除算環はp正則。完備化や完全忠実平坦性は仮定・結論に含めない。 -/
theorem deltaPDivisionTwoStep_p_mul_injective
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
    Function.Injective (fun b : DeltaAdjoinDivision E₀ (p : B₀)
      (fun _ : σ ↦ (E₀).frobeniusLift (j₀ y₁)) ↦
      (p : DeltaAdjoinDivision E₀ (p : B₀) (fun _ : σ ↦ (E₀).frobeniusLift (j₀ y₁))) * b) := by
  exact deltaPDivisionRaw_p_mul_injective (σ := σ) E₀ (j₀ y₁)
    (deltaPDivisionRaw_p_mul_injective (σ := σ) D y₀ hpA hg₀ w hw hy₀)
    hg₁ (w.map j₀) (deltaPDivisionRaw_delta_prime_unit_map (σ := σ) D y₀ w hw)
    (deltaPDivisionRaw_next_isSMulRegular (σ := σ) D y₀ y₁ hpA hg₀ w hw hy₁)

end SerrePositivity.BhattScholze
