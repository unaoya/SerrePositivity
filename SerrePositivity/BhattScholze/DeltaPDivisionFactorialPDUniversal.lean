module

public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialPDLift

/-! # p正則な分冪標的に対する分冪射の普遍性

具体的階乗部分環と正次数イデアルを使用する。標的のp正則性を明示する。
一般の分冪包や導来比較の構築は含まない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}

/-- 実延長射は正次数階乗イデアルを指定された分冪イデアルへ写す。 -/
theorem pDivisionFactorialLiftToPDTarget_ideal_le
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) :
    (pDivisionFactorialIdeal p y).map
      (pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy) ≤ I := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, n⟩, rfl⟩
  change pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy _ ∈ I
  rw [pDivisionFactorialLiftToPDTarget_value]
  exact H.dpow_mem (Nat.succ_ne_zero n) (hy s)

/-- 任意のp正則分冪標的への実延長射は全分冪を保つ。 -/
theorem pDivisionFactorialLiftToPDTarget_isDPMorphism
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    (D : DeltaStructure p A) {I : Ideal B} (H : DividedPowers I)
    (f : A →+* B) (y : σ → A) (hy : ∀ s, f (y s) ∈ I) :
    DividedPowers.IsDPMorphism (pDivisionFactorialIdealDividedPowers hA D y) H
      (pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy) := by
  let g := pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy
  let HA := pDivisionFactorialIdealDividedPowers hA D y
  have hI := pDivisionFactorialLiftToPDTarget_ideal_le hA hB hpB H f y hy
  refine ⟨hI, ?_⟩
  intro n a ha
  have hb : g a ∈ I := hI (Ideal.mem_map_of_mem g ha)
  have he : (n.factorial : B) * H.dpow n (g a) = (n.factorial : B) * g (HA.dpow n a) := by
    calc
      _ = (g a) ^ n := H.factorial_mul_dpow_eq_pow hb
      _ = g (a ^ n) := (map_pow g a n).symm
      _ = g ((n.factorial : pDivisionFactorialSubring p y) * HA.dpow n a) :=
        congrArg g (HA.factorial_mul_dpow_eq_pow ha).symm
      _ = _ := by rw [map_mul, map_natCast]
  have hi : Function.Injective (algebraMap B (Localization.Away (p : B))) := by
    intro x z h
    exact pDivisionFactorialBase_injective hpB (fun _ : Unit ↦ (0 : B)) (Subtype.ext h)
  apply hi
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hB n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  simpa only [map_mul, map_natCast] using
    congrArg (algebraMap B (Localization.Away (p : B))) he

/-- p正則な分冪標的に対し、基底射を延長する分冪射が一意に存在する。 -/
theorem existsUnique_pDivisionFactorialDPMorphism
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    (D : DeltaStructure p A) {I : Ideal B} (H : DividedPowers I)
    (f : A →+* B) (y : σ → A) (hy : ∀ s, f (y s) ∈ I) :
    ∃! F : pDivisionFactorialSubring p y →+* B,
      F.comp (pDivisionFactorialBase p y) = f ∧
        DividedPowers.IsDPMorphism (pDivisionFactorialIdealDividedPowers hA D y) H F := by
  refine ⟨pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy,
    ⟨pDivisionFactorialLiftToPDTarget_comp_base hA hB hpB H f y hy,
      pDivisionFactorialLiftToPDTarget_isDPMorphism hA hB hpB D H f y hy⟩, ?_⟩
  intro F hF
  exact (existsUnique_pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy).unique hF.1
    (pDivisionFactorialLiftToPDTarget_comp_base hA hB hpB H f y hy)

end SerrePositivity.BhattScholze
