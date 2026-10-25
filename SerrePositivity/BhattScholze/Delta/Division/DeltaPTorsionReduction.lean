module

public import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionUniversal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # p冪ねじれのδ安定性と除去商のp正則性

p局所化への核を再利用する。新しいねじれイデアルは定義しない。
完備化後の正則性は別工程。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- pの冪の分母集合は任意のδ環のFrobeniusで安定。 -/
theorem powers_p_frobenius_stable (D : DeltaStructure p A)
    (s : Submonoid.powers (p : A)) : D.frobeniusLift s ∈ Submonoid.powers (p : A) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : A) (p : A)).mp s.property
  rw [← hn, map_pow, map_natCast]
  exact Submonoid.pow_mem _ (Submonoid.mem_powers _) n

/-- p局所化への核、すなわちp冪ねじれイデアルはδ安定。 -/
theorem isStable_ker_away_p (D : DeltaStructure p A) :
    D.IsStable (RingHom.ker (algebraMap A (Localization.Away (p : A)))) :=
  (D.isDeltaHom_localization (Submonoid.powers (p : A)) (Localization.Away (p : A))
    D.powers_p_frobenius_stable).isStable_ker

/-- p冪ねじれをδ閉包してもイデアルは増えない。 -/
theorem deltaClosure_ker_away_p (D : DeltaStructure p A) :
    D.deltaClosure (RingHom.ker (algebraMap A (Localization.Away (p : A)))) =
      RingHom.ker (algebraMap A (Localization.Away (p : A))) :=
  D.deltaClosure_eq D.isStable_ker_away_p

/-- p冪ねじれのδ閉包商ではpは正則。 -/
theorem p_mul_injective_torsionReduction (D : DeltaStructure p A) :
    Function.Injective (fun x :
      A ⧸ D.deltaClosure (RingHom.ker (algebraMap A (Localization.Away (p : A)))) ↦
        (p : A ⧸ D.deltaClosure
          (RingHom.ker (algebraMap A (Localization.Away (p : A))))) * x) := by
  rw [D.deltaClosure_ker_away_p]
  let j := algebraMap A (Localization.Away (p : A))
  intro x y hxy
  apply RingHom.kerLift_injective j
  have h := congrArg (RingHom.kerLift j) hxy
  simp only [map_mul, map_natCast] at h
  have hp : IsUnit (p : Localization.Away (p : A)) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (p : A)
  exact hp.mul_left_cancel h

/-- 除数の具体的な表示がpに等しい場合にも同じδ商のp正則性を使える。 -/
theorem p_mul_injective_torsionReduction_of_eq_p (D : DeltaStructure p A)
    (d : A) (hd : d = (p : A)) :
    Function.Injective (fun x :
      A ⧸ D.deltaClosure (RingHom.ker (algebraMap A (Localization.Away d))) ↦
        (p : A ⧸ D.deltaClosure (RingHom.ker (algebraMap A (Localization.Away d)))) * x) := by
  subst d
  exact D.p_mul_injective_torsionReduction

end SerrePositivity.BhattScholze.DeltaStructure

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- p除算添加後の既存旧ねじれ除去商はp正則。完備化前の具体的候補。 -/
theorem deltaDivisionTorsionQuotient_p_mul_injective
    (D : DeltaStructure p A) (a : σ → A) :
    Function.Injective (fun x : DeltaDivisionTorsionQuotient D (p : A) a ↦
      (p : DeltaDivisionTorsionQuotient D (p : A) a) * x) := by
  exact (deltaAdjoinDivisionStructure D (p : A) a).p_mul_injective_torsionReduction_of_eq_p
    (deltaAdjoinDivisionMap D (p : A) a (p : A)) (map_natCast _ _)

end SerrePositivity.BhattScholze
