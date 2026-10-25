module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivisionReindex
public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivisionEmpty
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionFamilyStep
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootPowerSubsetBaseQuotient

/-! # 独立根関係の任意有限族のraw p除算包のp正則性 -/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

/-- 有限先行集合と一元添字の直和は一添字追加後の集合に標準同定される。 -/
def deltaRootFiniteInsertIndexEquiv {σ : Type v} [DecidableEq σ] {η : Type w} [Unique η]
    (T : Finset σ) (s : σ) (hs : s ∉ T) : (T : Type v) ⊕ η ≃ (insert s T : Finset σ) := by
  classical
  exact
    { toFun := fun r ↦ match r with
        | Sum.inl t => ⟨t, Finset.mem_insert_of_mem t.property⟩
        | Sum.inr _ => ⟨s, Finset.mem_insert_self s T⟩
      invFun := fun r ↦ if h : (r : σ) ∈ T then Sum.inl ⟨r, h⟩ else Sum.inr default
      left_inv := by
        intro r
        cases r with
        | inl t => dsimp; rw [ite_eq_left t.property]
        | inr r =>
          dsimp
          rw [dite_eq_right hs]
          congr 1
          exact Subsingleton.elim _ _
      right_inv := by
        intro r
        by_cases h : (r : σ) ∈ T
        · dsimp
          rw [dite_eq_left h]
        · dsimp
          rw [dite_eq_right h]
          apply Subtype.ext
          exact ((Finset.mem_insert.mp r.property).resolve_right h).symm }

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable {η : Type (max u v)} [Unique η]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b

/-- 任意有限集合の独立根関係のFrobenius像を同時p除算したraw環はp正則。
各有限先行集合の二種類のghost単射は明示仮定として保持する。 -/
theorem deltaRootFiniteRaw_p_mul_injective
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
        (R := DeltaAdjoinDivision E (p : P) (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
      ℕ → RelativeFreeDeltaRing
        (R := DeltaAdjoinDivision E (p : P) (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (T : Finset σ) :
    Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
      (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
      (p : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) := by
  classical
  have hpP : Function.Injective (fun z : P ↦ (p : P) * z) := by
    have h : IsSMulRegular A (p : A) := hpA
    have h' : IsSMulRegular P (p : P) := by simpa only [map_natCast] using h.of_flat (S := P)
    exact h'
  let wP := w.map (MvPolynomial.C : A →+* P).toMonoidHom
  have hwP : (wP : P) = (E).delta (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  induction T using Finset.induction_on with
  | empty =>
    let e := deltaAdjoinDivisionEmptyEquiv E (p : P)
      (fun t : (∅ : Finset σ) ↦ DeltaStructure.frobeniusLift E (r t))
    intro z t hzt
    apply e.injective
    apply hpP
    simpa only [map_mul, map_natCast] using congrArg e hzt
  | @insert s T hs ih =>
    have hx : IsSMulRegular
        (P ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : P) (fun t : T ↦ r t ^ p))
        (Ideal.Quotient.mk
          (deltaDivisionFirstBaseIdeal (p := p) (p : P) (fun t : T ↦ r t ^ p)) (r s)) := by
      have hpp : Ideal.span {(p : P), (p : P)} = Ideal.span {(p : P)} :=
        congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : P)))
      rw [deltaDivisionFirstBaseIdeal, hpp]
      exact deltaRootPowerSubsetModP_remaining_isSMulRegular (p := p) (T : Set σ) b s hs
    have hstep := deltaPDivisionFamilySum_p_mul_injective (η := η) E (fun t : T ↦ r t)
      (r s) hpP ih (hg₀ T) (hg₁ T ih) wP hwP hx
    let ρ := deltaRootFiniteInsertIndexEquiv (η := η) T s hs
    let e := deltaAdjoinDivisionReindexEquiv E (p : P)
      (Sum.elim (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))
        (fun _ : η ↦ DeltaStructure.frobeniusLift E (r s)))
      (fun t : (insert s T : Finset σ) ↦ DeltaStructure.frobeniusLift E (r t)) ρ
      (fun t ↦ by cases t <;> rfl)
    intro z t hzt
    apply e.symm.injective
    apply hstep
    simpa only [map_mul, map_natCast] using congrArg e.symm hzt

end SerrePositivity.BhattScholze
