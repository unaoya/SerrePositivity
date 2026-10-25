module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaAdjoinDivisionResidueRegular

/-! # Frobenius入力の係数イデアルと次のp除算入力の正則性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- φ(y_s)とy_s^pはpの倍数だけ異なり、raw残余の適切な係数イデアルは同じ。 -/
theorem deltaPDivisionFirstBaseIdeal_frobenius_eq_power (D : DeltaStructure p A) (y : σ → A) :
    deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ D.frobeniusLift (y s)) =
      deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p) := by
  let I := deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ D.frobeniusLift (y s))
  let J := deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p)
  have hpI : (p : A) ∈ I := by
    apply (show Ideal.span {(p : A), (p : A)} ≤ I from le_sup_left)
    exact Ideal.subset_span (by simp)
  have hpJ : (p : A) ∈ J := by
    apply (show Ideal.span {(p : A), (p : A)} ≤ J from le_sup_left)
    exact Ideal.subset_span (by simp)
  apply le_antisymm
  · refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro t ⟨s, rfl⟩
    change D.frobeniusLift (y s) ∈ J
    rw [D.frobeniusLift_apply]
    have hs : y s ^ p ∈ J := by
      apply (show Ideal.span (Set.range (fun s ↦ y s ^ p)) ≤ J from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
    exact J.add_mem hs (J.mul_mem_right (D.delta (y s)) hpJ)
  · refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro t ⟨s, rfl⟩
    change y s ^ p ∈ I
    have hs : D.frobeniusLift (y s) ∈ I := by
      apply (show Ideal.span (Set.range (fun s ↦ D.frobeniusLift (y s))) ≤ I from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
    have he : y s ^ p = D.frobeniusLift (y s) - (p : A) * D.delta (y s) := by
      rw [D.frobeniusLift_apply, add_sub_cancel_right]
    rw [he]
    exact I.sub_mem hs (I.mul_mem_right (D.delta (y s)) hpI)

omit [Fact p.Prime] in
/-- 定数一元族のp乗入力に対する係数イデアルは、具体的な(p,y^p)。 -/
theorem deltaPDivisionFirstBaseIdeal_const_power [Nonempty σ] (y : A) :
    deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun _ : σ ↦ y ^ p) =
      Ideal.span {(p : A), y ^ p} := by
  rw [deltaDivisionFirstBaseIdeal, Set.range_const]
  have hp : Ideal.span {(p : A), (p : A)} = Ideal.span {(p : A)} :=
    congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : A)))
  rw [hp, ← Ideal.span_insert]

/-- A/(p,y_s^p)で正則な元の像は、任意元族raw A{φ(y_s)/p}の実p商でも正則。 -/
theorem deltaPDivisionRawModP_next_isSMulRegular
    (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (y : σ → A) (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (x : A)
    (hx : IsSMulRegular
      (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p))
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p)) x)) :
    IsSMulRegular
      (DeltaAdjoinDivision D (p : A) (fun s ↦ D.frobeniusLift (y s)) ⧸
        Ideal.span {(p : DeltaAdjoinDivision D (p : A) (fun s ↦ D.frobeniusLift (y s)))})
      (Ideal.Quotient.mk
        (Ideal.span {(p : DeltaAdjoinDivision D (p : A) (fun s ↦ D.frobeniusLift (y s)))})
        (deltaAdjoinDivisionMap D (p : A) (fun s ↦ D.frobeniusLift (y s)) x)) := by
  let e := Ideal.quotEquivOfEq (deltaPDivisionFirstBaseIdeal_frobenius_eq_power D y)
  have hr : IsSMulRegular
      (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ D.frobeniusLift (y s)))
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A)
        (fun s ↦ D.frobeniusLift (y s))) x) := by
    intro z t hzt
    change Ideal.Quotient.mk _ x * z = Ideal.Quotient.mk _ x * t at hzt
    apply e.injective
    apply hx
    change Ideal.Quotient.mk _ x * e z = Ideal.Quotient.mk _ x * e t
    have h := congrArg e hzt
    rw [map_mul, map_mul, Ideal.quotEquivOfEq_mk] at h
    exact h
  exact deltaAdjoinDivisionModP_next_isSMulRegular D hpA hg
    (fun s ↦ D.frobeniusLift (y s)) w hw x hr

end SerrePositivity.BhattScholze
