module

public import SerrePositivity.BhattScholze.RankOneDPBasis
public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialPDTarget
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # p局所・p正則な環上の一元分冪代数の基底とp正則性 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 具体的p局所化に評価して得られる、p局所・p正則係数での実分冪基底。 -/
def rankOneDPPrimeBasis (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) :
    Module.Basis ℕ A (DividedPowerAlgebra A A) := by
  letI : Algebra ℚ (Localization.Away (p : A)) :=
    DeltaStructure.primeDividedPowersAwayRatAlgebra hA
  exact rankOneDPBasis (Localization.Away (p : A)) (fun x z h ↦
    pDivisionFactorialBase_injective hpA (fun _ : Unit ↦ (0 : A)) (Subtype.ext h))

/-- p局所係数での実基底の各元は、元のγ_n(1)そのもの。 -/
theorem rankOneDPPrimeBasis_apply (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (n : ℕ) :
    rankOneDPPrimeBasis hA hpA n = DividedPowerAlgebra.dp A n (1 : A) := by
  dsimp only [rankOneDPPrimeBasis, rankOneDPBasis]
  exact Module.Basis.mk_apply _ _ _

/-- 既存一元分冪代数の、p局所・p正則な元の環上の自由性。 -/
theorem rankOneDPPrime_moduleFree (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) :
    Module.Free A (DividedPowerAlgebra A A) :=
  Module.Free.of_basis (rankOneDPPrimeBasis hA hpA)

/-- p局所・p正則な環の既存一元分冪代数もp正則。 -/
theorem rankOneDPPrime_p_mul_injective (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) :
    Function.Injective (fun b : DividedPowerAlgebra A A ↦ (p : DividedPowerAlgebra A A) * b) := by
  let : Module.Free A (DividedPowerAlgebra A A) := rankOneDPPrime_moduleFree hA hpA
  have hr : IsRegular (p : A) := ⟨hpA, by
    intro x z h
    apply hpA
    simpa only [mul_comm] using h⟩
  have h := Module.Flat.isSMulRegular_of_isRegular (M := DividedPowerAlgebra A A) hr
  simpa only [IsSMulRegular, Algebra.smul_def, map_natCast] using h

end SerrePositivity.BhattScholze
