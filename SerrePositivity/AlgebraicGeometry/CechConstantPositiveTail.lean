module

public import SerrePositivity.AlgebraicGeometry.CechConstantComplex
public import SerrePositivity.AlgebraicGeometry.CochainComplexOfExactness

/-!
概要：元の定数列の正次数だけを残す同じ商とその完全性。
方針：零次を零加群にし、元の0/id微分と既存の正次数完全性を使う。
規約：元の正次数の各項・微分と係数の宇宙を保つ。
使われ方：F8の全複体から余分な定数基底列を除く比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {R : Type v} [CommRing R] (A : ModuleCat.{u} R)

/-- 元の定数列の零次だけを零加群に置き換える。 -/
def cechConstantPositiveTailTerm : ℕ → ModuleCat.{u} R
  | 0 => 0
  | _ + 1 => A

/-- 正次数の微分は同じ元の定数列の微分。 -/
def cechConstantPositiveTailD :
    ∀ n, cechConstantPositiveTailTerm A n ⟶ cechConstantPositiveTailTerm A (n + 1)
  | 0 => 0
  | n + 1 => (cechConstantComplex A).d (n + 1) (n + 2)

/-- 同じ正次数の微分の二乗も零。 -/
theorem cechConstantPositiveTailD_squared (n : ℕ) :
    cechConstantPositiveTailD A n ≫ cechConstantPositiveTailD A (n + 1) = 0 := by
  cases n with
  | zero => exact zero_comp
  | succ n => exact (cechConstantComplex A).d_comp_d (n + 1) (n + 2) (n + 3)

/-- 同じ定数列の正次数を残した複体。 -/
def cechConstantPositiveTail : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (cechConstantPositiveTailTerm A) (cechConstantPositiveTailD A)
    (cechConstantPositiveTailD_squared A)

set_option backward.isDefEq.respectTransparency false in
/-- 元の定数列の正次数の商は、同じ微分で完全。 -/
theorem cechConstantPositiveTail_acyclic : (cechConstantPositiveTail A).Acyclic := by
  apply cochainComplexOf_acyclic_of_injective_exact _ _ (cechConstantPositiveTailD_squared A)
  · intro x y _
    exact (ModuleCat.subsingleton_of_isZero (isZero_zero (ModuleCat.{u} R))).elim x y
  · intro n
    cases n with
    | zero =>
      change Function.Exact (0 : (0 : ModuleCat.{u} R) →ₗ[R] A)
        ((cechConstantComplex A).d 1 2).hom
      rw [cechConstantComplex_d, ite_eq_right (show ¬ Even 3 by decide)]
      exact (LinearMap.exact_zero_iff_injective (0 : ModuleCat.{u} R) LinearMap.id).mpr
        Function.injective_id
    | succ n =>
      have h := cechConstantComplex_exact A (n + 1)
      rw [(cechConstantComplex A).exactAt_iff' (n + 1) (n + 2) (n + 3)
        (by simp) (by simp)] at h
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h

/-- 元の定数列から同じ正次数の商への各成分。 -/
def cechConstantPositiveTailProjectionComponent :
    ∀ n, (cechConstantComplex A).X n ⟶ (cechConstantPositiveTail A).X n
  | 0 => 0
  | _ + 1 => 𝟙 A

set_option backward.isDefEq.respectTransparency false in
/-- 元の定数列から同じ正次数の商への射影。 -/
def cechConstantPositiveTailProjection : cechConstantComplex A ⟶ cechConstantPositiveTail A :=
  CochainComplex.ofHom (cechConstantPositiveTailProjectionComponent A) (by
    intro n
    cases n with
    | zero =>
      change 0 ≫ _ = (cechConstantComplex A).d 0 1 ≫ 𝟙 A
      rw [cechConstantComplex_d, ite_eq_left (show Even 2 by decide), zero_comp, zero_comp]
    | succ n =>
      change 𝟙 A ≫ (cechConstantPositiveTail A).d (n + 1) (n + 2) =
        (cechConstantComplex A).d (n + 1) (n + 2) ≫ 𝟙 A
      have h : (cechConstantPositiveTail A).d (n + 1) (n + 2) =
          (cechConstantComplex A).d (n + 1) (n + 2) := CochainComplex.of_d _ _ _
      exact (Category.id_comp _).trans (h.trans (Category.comp_id _).symm))

/-- 同じ正次数の商への各成分は全射。 -/
theorem cechConstantPositiveTailProjection_surjective (n : ℕ) :
    Function.Surjective ((cechConstantPositiveTailProjection A).f n).hom := by
  cases n with
  | zero =>
    haveI : Epi ((cechConstantPositiveTailProjection A).f 0) := (isZero_zero _).epi _
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  | succ n =>
    change Function.Surjective (LinearMap.id : A →ₗ[R] A)
    exact Function.surjective_id

end SerrePositivity.AlgebraicGeometry
