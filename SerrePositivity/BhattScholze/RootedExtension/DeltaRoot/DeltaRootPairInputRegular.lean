module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootPowerSubsetBaseQuotient

/-! # 二つの独立した根関係のraw除算への正則入力 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意の根関係は、実際の多項式環のmod p商で正則。 -/
theorem deltaRootRelation_modP_isSMulRegular (b : σ → A) (s : σ) :
    IsSMulRegular (MvPolynomial σ A ⧸ Ideal.span {(p : MvPolynomial σ A)})
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial σ A)})
        (deltaRootRelationFamily (p := p) b s)) := by
  have h := deltaRootPowerSubsetModP_remaining_isSMulRegular (p := p) (∅ : Set σ) b s
    (by simp)
  have hJ : Set.range (fun r : (∅ : Set σ) ↦ (deltaRootRelationFamily (p := p) b r) ^ p) =
      ∅ := by
    ext z
    constructor
    · rintro ⟨r, _⟩
      exact r.property.elim
    · intro hz
      exact hz.elim
  rw [hJ, Ideal.span_empty, sup_bot_eq] at h
  exact h

/-- 異なる二つの根関係について、後者は(p,前者のp乗)の実商で正則。 -/
theorem deltaRootRelation_pairPower_modP_isSMulRegular
    (b : σ → A) (s t : σ) (hts : t ≠ s) :
    IsSMulRegular
      (MvPolynomial σ A ⧸ Ideal.span
        {(p : MvPolynomial σ A), (deltaRootRelationFamily (p := p) b s) ^ p})
      (Ideal.Quotient.mk
        (Ideal.span {(p : MvPolynomial σ A), (deltaRootRelationFamily (p := p) b s) ^ p})
        (deltaRootRelationFamily (p := p) b t)) := by
  have h := deltaRootPowerSubsetModP_remaining_isSMulRegular (p := p) ({s} : Set σ) b t
    (by simpa using hts)
  have hJ : Set.range (fun r : ({s} : Set σ) ↦ (deltaRootRelationFamily (p := p) b r) ^ p) =
      {(deltaRootRelationFamily (p := p) b s) ^ p} := by
    ext z
    constructor
    · rintro ⟨⟨r, hr⟩, rfl⟩
      have hrs : r = s := Set.mem_singleton_iff.mp hr
      subst r
      exact Set.mem_singleton _
    · intro hz
      have hz' := Set.mem_singleton_iff.mp hz
      exact ⟨⟨s, Set.mem_singleton _⟩, hz'.symm⟩
  rw [hJ, ← Ideal.span_insert] at h
  exact h

end SerrePositivity.BhattScholze
