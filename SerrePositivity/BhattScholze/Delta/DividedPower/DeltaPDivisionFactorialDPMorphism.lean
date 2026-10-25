module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialMap

/-! # 具体的階乗部分環の誘導環射の分冪射性

イデアルの全元の全分冪を保つことを階乗の消去で確認する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}

/-- 基底環射に沿う実誘導環射は、正次数階乗イデアルの全分冪を保つ。 -/
theorem pDivisionFactorialMap_isDPMorphism
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B)) (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (y : σ → A) :
    DividedPowers.IsDPMorphism (pDivisionFactorialIdealDividedPowers hA D y)
      (pDivisionFactorialIdealDividedPowers hB E (fun s ↦ f (y s)))
      (pDivisionFactorialMap hA f y) := by
  let g := pDivisionFactorialMap hA f y
  let HA := pDivisionFactorialIdealDividedPowers hA D y
  let HB := pDivisionFactorialIdealDividedPowers hB E (fun s ↦ f (y s))
  let S := pDivisionFactorialSubring p (fun s ↦ f (y s))
  let L := Localization.Away (p : B)
  have hI := pDivisionFactorialMap_ideal_le hA f y
  refine ⟨hI, ?_⟩
  intro n a ha
  have hb : g a ∈ pDivisionFactorialIdeal p (fun s ↦ f (y s)) :=
    hI (Ideal.mem_map_of_mem g ha)
  have he : (n.factorial : S) * HB.dpow n (g a) = (n.factorial : S) * g (HA.dpow n a) := by
    calc
      _ = (g a) ^ n := HB.factorial_mul_dpow_eq_pow hb
      _ = g (a ^ n) := (map_pow g a n).symm
      _ = g ((n.factorial : pDivisionFactorialSubring p y) * HA.dpow n a) :=
        congrArg g (HA.factorial_mul_dpow_eq_pow ha).symm
      _ = _ := by rw [map_mul, map_natCast]
  apply Subtype.ext
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hB n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  exact congrArg (fun t : S ↦ (t : L)) he

end SerrePositivity.BhattScholze
