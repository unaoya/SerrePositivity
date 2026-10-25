module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialPDTarget
public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFactorialFunctorial

/-! # p正則な分冪標的への具体的階乗部分環の延長射

標的のp正則性を明示する。pねじれのある一般分冪標的の普遍性は主張しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}

/-- 具体的部分環内でも、階乗を掛けると元の通常冪に戻る。 -/
theorem pDivisionFactorialValue_factorial_mul
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (y : σ → A) (s : σ) (n : ℕ) :
    (n.factorial : pDivisionFactorialSubring p y) *
        ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ =
      pDivisionFactorialBase p y (y s) ^ n := by
  apply Subtype.ext
  change (n.factorial : Localization.Away (p : A)) *
    (Ring.inverse (n.factorial : Localization.Away (p : A)) * _) = _
  rw [← mul_assoc, Ring.mul_inverse_cancel _
    (DeltaStructure.primeDividedPowersAwayNat_isUnit hA n.factorial
      (Nat.factorial_ne_zero n)), one_mul]
  rfl

/-- 基底射を延長する、p正則分冪標的への実環射。 -/
def pDivisionFactorialLiftToPDTarget
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) : pDivisionFactorialSubring p y →+* B :=
  (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H (fun s ↦ f (y s)) hy).symm.toRingHom.comp
    (pDivisionFactorialMap hA f y)

/-- 実延長射は指定された基底射を延長する。 -/
theorem pDivisionFactorialLiftToPDTarget_comp_base
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) :
    (pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy).comp
      (pDivisionFactorialBase p y) = f := by
  ext a
  change (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H (fun s ↦ f (y s)) hy).symm
    (pDivisionFactorialMap hA f y (pDivisionFactorialBase p y a)) = f a
  have hf := RingHom.congr_fun (pDivisionFactorialMap_comp_base hA f y) a
  simp only [RingHom.comp_apply] at hf
  rw [hf]
  exact (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H
    (fun s ↦ f (y s)) hy).symm_apply_apply (f a)

/-- 実延長射は全階乗生成元を指定の分冪値へ送る。 -/
theorem pDivisionFactorialLiftToPDTarget_value
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) (s : σ) (n : ℕ) :
    pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy
      ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ =
      H.dpow n (f (y s)) := by
  change (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H (fun s ↦ f (y s)) hy).symm
    (pDivisionFactorialMap hA f y _) = _
  rw [pDivisionFactorialMap_value]
  apply (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H (fun s ↦ f (y s)) hy).injective
  rw [RingEquiv.apply_symm_apply]
  apply Subtype.ext
  exact pDivisionFactorialValue_eq_dpow_image hB H (fun s ↦ f (y s)) hy s n

/-- p正則な標的への環射は、基底上の値のみで一意に決まる。 -/
theorem pDivisionFactorialHom_ext_of_p_regular
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b)) (y : σ → A)
    (F G : pDivisionFactorialSubring p y →+* B)
    (hbase : ∀ a : A, F (pDivisionFactorialBase p y a) = G (pDivisionFactorialBase p y a)) :
    F = G := by
  apply pDivisionFactorialHom_ext y F G hbase
  intro s n
  let g : B →+* Localization.Away (p : B) := algebraMap B _
  have hi : Function.Injective g := by
    intro x z h
    exact pDivisionFactorialBase_injective hpB (fun _ : Unit ↦ (0 : B)) (Subtype.ext h)
  apply hi
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hB n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  have hF := congrArg F (pDivisionFactorialValue_factorial_mul hA y s n)
  have hG := congrArg G (pDivisionFactorialValue_factorial_mul hA y s n)
  simp only [map_mul, map_natCast, map_pow] at hF hG
  rw [hbase] at hF
  simpa only [map_mul, map_natCast] using congrArg g (hF.trans hG.symm)

/-- p正則な分冪標的への、指定の基底射を延長する環射の存在と一意性。 -/
theorem existsUnique_pDivisionFactorialLiftToPDTarget
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) :
    ∃! F : pDivisionFactorialSubring p y →+* B, F.comp (pDivisionFactorialBase p y) = f := by
  refine ⟨pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy,
    pDivisionFactorialLiftToPDTarget_comp_base hA hB hpB H f y hy, ?_⟩
  intro F hF
  apply pDivisionFactorialHom_ext_of_p_regular hA hB hpB y
  intro a
  exact (RingHom.congr_fun hF a).trans
    (RingHom.congr_fun (pDivisionFactorialLiftToPDTarget_comp_base hA hB hpB H f y hy) a).symm

end SerrePositivity.BhattScholze
