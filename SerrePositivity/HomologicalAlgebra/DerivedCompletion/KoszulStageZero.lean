module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulTower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulCanonicalZero
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # 各冪のKoszul複体のH⁰と商環の逆系

正則性を仮定せず、標準包含で正規化した同型により各段のH⁰を商加群へ同定する。
Koszulの遷移は、この同定の下で商環の標準的な遷移と一致する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 各元のn乗で生成されるイデアル。一般のイデアル冪と区別する。 -/
def powerKoszulIdeal {e : ℕ} (a : Fin e → R) (n : ℕ) : Ideal R :=
  Ideal.span (Set.range (fun i ↦ a i ^ n))

/-- 各段のH⁰の商加群との同型。正則性やねじれの有界性は不要。
標準包含の像を商の標準元に送る同型を使用する。 -/
def powerKoszulStageH0Equiv {e : ℕ} (a : Fin e → R) (n : ℕ) :
    (powerKoszulTower R a n).homology 0 ≃ₗ[R] R ⧸ powerKoszulIdeal R a n :=
  koszulCanonicalH0Equiv R (fun i ↦ a i ^ n)

@[simp] theorem powerKoszulStageH0Equiv_unit {e : ℕ} (a : Fin e → R) (n : ℕ) (r : R) :
    powerKoszulStageH0Equiv R a n (koszulH0Unit R (fun i ↦ a i ^ n) r) =
      Ideal.Quotient.mk _ r := koszulCanonicalH0Equiv_unit R _ r

/-- 元の冪を進めると、生成されるイデアルは小さくなる。 -/
theorem powerKoszulIdeal_antitone {e : ℕ} (a : Fin e → R) :
    Antitone (powerKoszulIdeal R a) := by
  intro m n hmn
  apply Ideal.span_le.mpr
  rintro z ⟨i, rfl⟩
  change a i ^ n ∈ powerKoszulIdeal R a m
  have heq : n = m + (n - m) := (Nat.add_sub_of_le hmn).symm
  rw [heq, pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))

/-- 冪による商環の標準的な遷移写像。 -/
def powerKoszulQuotientTransition {e : ℕ} (a : Fin e → R) (n : ℕ) :
    R ⧸ powerKoszulIdeal R a (n + 1) →+* R ⧸ powerKoszulIdeal R a n :=
  Ideal.Quotient.factor (powerKoszulIdeal_antitone R a (Nat.le_succ n))

@[simp] theorem powerKoszulQuotientTransition_mk {e : ℕ} (a : Fin e → R) (n : ℕ) (r : R) :
    powerKoszulQuotientTransition R a n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl

/-- 商環の遷移は全射。高次Koszulホモロジーの遷移にはこの結論を使用しない。 -/
theorem powerKoszulQuotientTransition_surjective {e : ℕ} (a : Fin e → R) (n : ℕ) :
    Function.Surjective (powerKoszulQuotientTransition R a n) :=
  Ideal.Quotient.factor_surjective _

/-- KoszulのH⁰遷移は、正規化された同定の下で商環の標準遷移と一致する。 -/
theorem powerKoszulStageH0Equiv_transition {e : ℕ} (a : Fin e → R) (n : ℕ)
    (x : (powerKoszulTower R a (n + 1)).homology 0) :
    powerKoszulStageH0Equiv R a n
      ((HomologicalComplex.homologyMap (powerKoszulTransition R a n) 0).hom x) =
      powerKoszulQuotientTransition R a n
        (powerKoszulStageH0Equiv R a (n + 1) x) := by
  obtain ⟨r, rfl⟩ := koszulH0Unit_surjective R (fun i ↦ a i ^ (n + 1)) x
  change koszulCanonicalH0Equiv R (fun i ↦ a i ^ n)
    ((HomologicalComplex.homologyMap (koszulComplexMapOfMul R
      (fun i ↦ a i ^ (n + 1)) (fun i ↦ a i ^ n) a
      (fun i ↦ pow_succ (a i) n)) 0).hom
      (koszulH0Unit R (fun i ↦ a i ^ (n + 1)) r)) =
    powerKoszulQuotientTransition R a n
      (koszulCanonicalH0Equiv R (fun i ↦ a i ^ (n + 1))
        (koszulH0Unit R (fun i ↦ a i ^ (n + 1)) r))
  rw [koszulH0Unit_mapOfMul, koszulCanonicalH0Equiv_unit, koszulCanonicalH0Equiv_unit]
  rfl

/-- H⁰に誘導されるKoszul遷移は全射。負次数についての主張ではない。 -/
theorem powerKoszulTransition_homology_zero_surjective {e : ℕ} (a : Fin e → R) (n : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap
      (powerKoszulTransition R a n) 0).hom := by
  intro x
  obtain ⟨r, rfl⟩ := koszulH0Unit_surjective R (fun i ↦ a i ^ n) x
  refine ⟨koszulH0Unit R (fun i ↦ a i ^ (n + 1)) r, ?_⟩
  exact koszulH0Unit_mapOfMul R _ _ _ _ r

end SerrePositivity.DerivedCompletion
