module

public import SerrePositivity.CommutativeAlgebra.DerivationDescent
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Kaehler.Basic

/-! # 微分が零の最小多項式と単純添加の導分

多項式の標準微分を評価の核に沿って降下し、生成元を1に送る導分を実構成する。
-/

@[expose] public section
namespace SerrePositivity
open Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- 最小多項式の微分が零なら、評価の核の元の微分も評価後に零。 -/
theorem aeval_derivative_eq_zero_of_minpoly_derivative_eq_zero
    (x : K) (h : derivative (minpoly F x) = 0) (f : F[X]) (hf : aeval x f = 0) :
    aeval x (derivative f) = 0 := by
  obtain ⟨g, rfl⟩ := (minpoly.dvd_iff.mpr hf)
  rw [derivative_mul, h, zero_mul, zero_add, map_mul, minpoly.aeval, zero_mul]

/-- 冪基底の生成元を1に送る実際の導分。 -/
theorem _root_.PowerBasis.exists_generatorDerivation (B : PowerBasis F K)
    (h : derivative (minpoly F B.gen) = 0) :
    ∃ δ : Derivation F K K, ∀ f : F[X], δ (aeval B.gen f) = aeval B.gen (derivative f) := by
  let : Algebra F[X] K := (aeval B.gen).toRingHom.toAlgebra
  let : IsScalarTower F F[X] K := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    change algebraMap F K r = aeval B.gen (C r)
    simp)
  have hs : Function.Surjective (algebraMap F[X] K) := by
    intro x
    obtain ⟨f, hf⟩ := B.exists_eq_aeval' x
    exact ⟨f, hf.symm⟩
  let δ := Polynomial.mkDerivation F (1 : K)
  have hk : ∀ f, algebraMap F[X] K f = 0 → δ f = 0 := by
    intro f hf
    rw [Polynomial.mkDerivation_apply, Algebra.smul_def, mul_one]
    exact aeval_derivative_eq_zero_of_minpoly_derivative_eq_zero B.gen h f hf
  refine ⟨descendDerivation hs δ hk, ?_⟩
  intro f
  change descendDerivation hs δ hk (algebraMap F[X] K f) = _
  rw [descendDerivation_apply, Polynomial.mkDerivation_apply, Algebra.smul_def, mul_one]
  rfl

/-- 生成元を1に送る導分を、構成済みの存在定理から選ぶ。 -/
noncomputable def _root_.PowerBasis.generatorDerivation (B : PowerBasis F K)
    (h : derivative (minpoly F B.gen) = 0) : Derivation F K K :=
  (B.exists_generatorDerivation h).choose

/-- この導分は多項式の評価と微分を両立させる。 -/
theorem _root_.PowerBasis.generatorDerivation_aeval (B : PowerBasis F K)
    (h : derivative (minpoly F B.gen) = 0) (f : F[X]) :
    B.generatorDerivation h (aeval B.gen f) = aeval B.gen (derivative f) :=
  (B.exists_generatorDerivation h).choose_spec f

@[simp] theorem _root_.PowerBasis.generatorDerivation_gen (B : PowerBasis F K)
    (h : derivative (minpoly F B.gen) = 0) : B.generatorDerivation h B.gen = 1 := by
  have := B.generatorDerivation_aeval h X
  simpa using this

/-- 構成した導分で検出できるため、生成元の通常微分は非零。 -/
theorem _root_.PowerBasis.kaehlerDifferential_gen_ne_zero (B : PowerBasis F K)
    (h : derivative (minpoly F B.gen) = 0) : KaehlerDifferential.D F K B.gen ≠ 0 := by
  intro hzero
  have heq := congrArg (B.generatorDerivation h).liftKaehlerDifferential hzero
  simp at heq

end SerrePositivity
