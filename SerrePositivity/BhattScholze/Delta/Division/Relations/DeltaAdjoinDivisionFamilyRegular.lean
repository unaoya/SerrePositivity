module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivisionFiniteColimitEquiv

/-! # 有限部分族から任意族raw包へのp正則性の移送 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- 全有限部分族のp正則性から、その環余極限のp正則性を得る。遷移の単射性は不要。 -/
theorem deltaAdjoinDivisionFiniteColimit_p_mul_injective
    (hp : ∀ T : Finset σ, Function.Injective
      (fun z : DeltaAdjoinDivisionFiniteStage D d a T ↦
        (p : DeltaAdjoinDivisionFiniteStage D d a T) * z)) :
    Function.Injective (fun z : DeltaAdjoinDivisionFiniteColimit D d a ↦
      (p : DeltaAdjoinDivisionFiniteColimit D d a) * z) := by
  classical
  intro x y hxy
  change (p : DeltaAdjoinDivisionFiniteColimit D d a) * x =
    (p : DeltaAdjoinDivisionFiniteColimit D d a) * y at hxy
  apply sub_eq_zero.mp
  have hz : (p : DeltaAdjoinDivisionFiniteColimit D d a) * (x - y) = 0 := by
    rw [mul_sub, hxy, sub_self]
  obtain ⟨T, z, hT⟩ := Ring.DirectLimit.exists_of (x - y)
  have hzero : deltaAdjoinDivisionFiniteColimitOf D d a T
      ((p : DeltaAdjoinDivisionFiniteStage D d a T) * z) = 0 := by
    rw [map_mul, map_natCast]
    change (p : DeltaAdjoinDivisionFiniteColimit D d a) *
      Ring.DirectLimit.of _ _ T z = 0
    rw [hT, hz]
  have hzero' : Ring.DirectLimit.of
      (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
      (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h) T
      ((p : DeltaAdjoinDivisionFiniteStage D d a T) * z) = 0 := hzero
  obtain ⟨U, hTU, hU⟩ := Ring.DirectLimit.of.zero_exact hzero'
  have hu : deltaAdjoinDivisionFiniteMap D d a hTU z = 0 := by
    apply hp U
    change (p : DeltaAdjoinDivisionFiniteStage D d a U) *
      deltaAdjoinDivisionFiniteMap D d a hTU z =
        (p : DeltaAdjoinDivisionFiniteStage D d a U) * 0
    rw [mul_zero]
    simpa only [map_mul, map_natCast] using hU
  calc
    x - y = deltaAdjoinDivisionFiniteColimitOf D d a T z := hT.symm
    _ = deltaAdjoinDivisionFiniteColimitOf D d a U
        (deltaAdjoinDivisionFiniteMap D d a hTU z) :=
      (deltaAdjoinDivisionFiniteColimitOf_compatible D d a hTU z).symm
    _ = 0 := by rw [hu, map_zero]

/-- 全有限部分族がp正則なら、任意族の実raw包自身がp正則。 -/
theorem deltaAdjoinDivisionFamily_p_mul_injective
    (hp : ∀ T : Finset σ, Function.Injective
      (fun z : DeltaAdjoinDivisionFiniteStage D d a T ↦
        (p : DeltaAdjoinDivisionFiniteStage D d a T) * z)) :
    Function.Injective (fun z : DeltaAdjoinDivision D d a ↦
      (p : DeltaAdjoinDivision D d a) * z) := by
  let e := deltaAdjoinDivisionFiniteColimitEquiv D d a
  intro x y hxy
  apply e.symm.injective
  apply deltaAdjoinDivisionFiniteColimit_p_mul_injective D d a hp
  simpa only [map_mul, map_natCast] using congrArg e.symm hxy

end SerrePositivity.BhattScholze
