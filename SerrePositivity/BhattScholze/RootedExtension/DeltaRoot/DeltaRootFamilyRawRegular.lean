module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootFiniteRawRegular
public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivisionFamilyRegular

/-! # 任意根関係族のraw p除算包のp正則性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable {η : Type (max u v)} [Unique η]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b

/-- 任意添字族のraw包は、有限部分集合版の証明と標準余極限比較からp正則となる。
ghost入力は先行raw包のp正則性を受け取る形で保持し、循環依存を作らない。 -/
theorem deltaRootFamilyRaw_p_mul_injective
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η)) :
    Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
      (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t)) ↦
      (p : DeltaAdjoinDivision E (p : P)
        (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t))) * z) := by
  apply deltaAdjoinDivisionFamily_p_mul_injective E (p : P)
    (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t))
  intro T
  exact deltaRootFiniteRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁ T

end SerrePositivity.BhattScholze
