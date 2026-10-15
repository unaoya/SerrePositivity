module

public import SerrePositivity.BhattScholze.DeltaRootPairInputRegular
public import SerrePositivity.BhattScholze.DeltaPDivisionPairRegular

/-! # 二つの独立根関係の具体的raw p除算包のp正則性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {σ : Type v} {η : Type (max u v)}
  [CommRing A] [Unique η]
variable (D : DeltaStructure p A) (b : σ → A) (s t : σ)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "rs" => deltaRootRelationFamily (p := p) b s
local notation "rt" => deltaRootRelationFamily (p := p) b t
local notation "a₀" => fun _ : η ↦ DeltaStructure.frobeniusLift E rs
local notation "a₁" => fun _ : η ↦ DeltaStructure.frobeniusLift E rt
local notation "B₀" => DeltaAdjoinDivision E (p : P) a₀

/-- p正則係数環の異なる二根関係のFrobenius像を同時p除算した実raw環はp正則。
各段のghost単射と指定単元δ(p)は明示し、入力関係の正則性は内部で供給する。 -/
theorem deltaRootPairRaw_p_mul_injective
    (hts : t ≠ s)
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) η) → ℕ → RelativeFreeDeltaRing (R := P) η))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B₀) η) → ℕ → RelativeFreeDeltaRing (R := B₀) η)) :
    Function.Injective (fun x : DeltaAdjoinDivision E (p : P) (Sum.elim a₀ a₁) ↦
      (p : DeltaAdjoinDivision E (p : P) (Sum.elim a₀ a₁)) * x) := by
  have hpP : Function.Injective (fun f : P ↦ (p : P) * f) := by
    have h : IsSMulRegular A (p : A) := hpA
    have h' := h.of_flat (S := P)
    have h'' : IsSMulRegular P (p : P) := by simpa only [map_natCast] using h'
    exact h''
  let wP := w.map (MvPolynomial.C : A →+* P).toMonoidHom
  have hwP : (wP : P) = (E).delta (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  exact deltaPDivisionPair_p_mul_injective (σ := η) E rs rt hpP hg₀ hg₁ wP hwP
    (deltaRootRelation_modP_isSMulRegular b s)
    (deltaRootRelation_pairPower_modP_isSMulRegular b s t hts)

end SerrePositivity.BhattScholze
