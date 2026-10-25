module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionNextInput
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionRawRegular

/-! # 任意先行族のraw p除算へ一入力を追加する正則性帰納 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {σ : Type v} {η : Type (max u v)}
  [CommRing A] [Unique η]
variable (D : DeltaStructure p A) (y : σ → A) (x : A)
local notation "a" => fun s ↦ D.frobeniusLift (y s)
local notation "B" => DeltaAdjoinDivision D (p : A) a
local notation "E" => deltaAdjoinDivisionStructure D (p : A) a
local notation "j" => deltaAdjoinDivisionMap D (p : A) a

/-- 任意先行族のp正則raw包へ次の一入力を除算添加した実二段環はp正則。 -/
theorem deltaPDivisionFamilyStep_p_mul_injective
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (hpB : Function.Injective (fun z : B ↦ (p : B) * z))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B) η) → ℕ → RelativeFreeDeltaRing (R := B) η))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hx : IsSMulRegular (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p))
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p)) x)) :
    Function.Injective (fun z : DeltaAdjoinDivision E (p : B)
      (fun _ : η ↦ DeltaStructure.frobeniusLift E (j x)) ↦
      (p : DeltaAdjoinDivision E (p : B)
        (fun _ : η ↦ DeltaStructure.frobeniusLift E (j x))) * z) := by
  let wB := w.map (j).toMonoidHom
  have hwB : (wB : B) = (E).delta (p : B) := by
    change j (w : A) = _
    rw [hw, deltaAdjoinDivisionMap_isDeltaHom D (p : A) a (p : A), map_natCast]
  exact deltaPDivisionRaw_p_mul_injective (σ := η) E (j x) hpB hg₁ wB hwB
    (deltaPDivisionRawModP_next_isSMulRegular D hpA hg₀ y w hw x hx)

/-- 任意先行族へ一入力を同時に加えたraw p除算包も、同じ具体的仮定でp正則。 -/
theorem deltaPDivisionFamilySum_p_mul_injective
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (hpB : Function.Injective (fun z : B ↦ (p : B) * z))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B) η) → ℕ → RelativeFreeDeltaRing (R := B) η))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hx : IsSMulRegular (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p))
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p)) x)) :
    Function.Injective (fun z : DeltaAdjoinDivision D (p : A)
      (Sum.elim a (fun _ : η ↦ D.frobeniusLift x)) ↦
      (p : DeltaAdjoinDivision D (p : A) (Sum.elim a (fun _ : η ↦ D.frobeniusLift x))) * z) := by
  let e := deltaAdjoinDivisionSumEquiv D (p : A) a (fun _ : η ↦ D.frobeniusLift x)
  have hφ : (fun _ : η ↦ j (D.frobeniusLift x)) =
      (fun _ : η ↦ DeltaStructure.frobeniusLift E (j x)) := by
    funext t
    exact (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a).map_frobeniusLift x
  have hpT : Function.Injective (fun z : DeltaAdjoinDivision E (j (p : A))
      (fun _ : η ↦ j (D.frobeniusLift x)) ↦
      (p : DeltaAdjoinDivision E (j (p : A)) (fun _ : η ↦ j (D.frobeniusLift x))) * z) := by
    rw [map_natCast, hφ]
    exact deltaPDivisionFamilyStep_p_mul_injective (η := η) D y x hpA hpB hg₀ hg₁ w hw hx
  intro z t hzt
  apply e.injective
  apply hpT
  simpa only [map_mul, map_natCast] using congrArg e hzt

end SerrePositivity.BhattScholze
