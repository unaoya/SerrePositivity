module

public import SerrePositivity.BhattScholze.PrincipalDPPresentation
public import SerrePositivity.BhattScholze.DeltaPDivisionFactorialIdeal

/-! # 一元分冪表示環から具体的階乗部分環への実全射

源のpねじれを許す。単射性や導来比較はこのファイルの結論には含まない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 実分冪構造への評価が与える、一元表示環から具体的階乗部分環への環射。 -/
def principalDPToFactorial (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : A) :
    PrincipalDPPresentation A y →+* pDivisionFactorialSubring p (fun _ : Unit ↦ y) := by
  letI : Algebra A (pDivisionFactorialSubring p (fun _ : Unit ↦ y)) :=
    (pDivisionFactorialBase p (fun _ : Unit ↦ y)).toAlgebra
  exact (principalDPEval (pDivisionFactorialIdealDividedPowers hA D (fun _ : Unit ↦ y)) y
    (pDivisionFactorialBase_mem_factorialIdeal (fun _ : Unit ↦ y) ())).toRingHom

/-- 表示環からの実射は、元のAからの基底射を保つ。 -/
theorem principalDPToFactorial_coeff (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y a : A) :
    principalDPToFactorial hA D y (algebraMap A (PrincipalDPPresentation A y) a) =
      pDivisionFactorialBase p (fun _ : Unit ↦ y) a := by
  let : Algebra A (pDivisionFactorialSubring p (fun _ : Unit ↦ y)) :=
    (pDivisionFactorialBase p (fun _ : Unit ↦ y)).toAlgebra
  exact AlgHom.commutes (principalDPEval
    (pDivisionFactorialIdealDividedPowers hA D (fun _ : Unit ↦ y)) y
    (pDivisionFactorialBase_mem_factorialIdeal (fun _ : Unit ↦ y) ())) a

/-- 各標準生成元の実像は、局所化内の指定された階乗分母。 -/
theorem principalDPToFactorial_generator (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : A) (n : ℕ) :
    principalDPToFactorial hA D y (principalDPGenerator y n) =
      ⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
        pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ := by
  let : Algebra A (pDivisionFactorialSubring p (fun _ : Unit ↦ y)) :=
    (pDivisionFactorialBase p (fun _ : Unit ↦ y)).toAlgebra
  have h := principalDPEval_generator
    (pDivisionFactorialIdealDividedPowers hA D (fun _ : Unit ↦ y)) y
    (pDivisionFactorialBase_mem_factorialIdeal (fun _ : Unit ↦ y) ()) n
  apply Subtype.ext
  change (principalDPEval
    (pDivisionFactorialIdealDividedPowers hA D (fun _ : Unit ↦ y)) y
    (pDivisionFactorialBase_mem_factorialIdeal (fun _ : Unit ↦ y) ())
    (principalDPGenerator y n) : Localization.Away (p : A)) = _
  rw [h]
  exact pDivisionFactorialIdealDividedPowers_base_apply hA D (fun _ : Unit ↦ y) () n

/-- 一元分冪表示環から具体的階乗部分環への実射は全射。 -/
theorem principalDPToFactorial_surjective (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : A) : Function.Surjective (principalDPToFactorial hA D y) := by
  let S := pDivisionFactorialSubring p (fun _ : Unit ↦ y)
  let F := principalDPToFactorial hA D y
  have hle : S ≤ (S.subtype.comp F).range := by
    apply Subring.closure_le.mpr
    rintro t (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
    · refine ⟨algebraMap A (PrincipalDPPresentation A y) a, ?_⟩
      exact congrArg Subtype.val (principalDPToFactorial_coeff hA D y a)
    · refine ⟨principalDPGenerator y n, ?_⟩
      exact congrArg Subtype.val (principalDPToFactorial_generator hA D y n)
  rintro ⟨t, ht⟩
  obtain ⟨b, hb⟩ := hle ht
  exact ⟨b, Subtype.ext hb⟩

end SerrePositivity.BhattScholze
