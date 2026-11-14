module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDFromGenerators
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBasis
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBaseChange
public import Mathlib.RingTheory.DividedPowers.RatAlgebra

/-!
# 自由分冪代数における基底の分冪の延長

## 概要
分冪基底上の自由分冪代数で、基底と自由変数の分冪を同じイデアルに入れる。

## 方針
係数を有理代数へ単射で写し、多項式の階乗表示を使う。
基底の分冪と自由分冪生成元からイデアル全体へ分冪を制限する。

## 規約
係数から有理代数への写像は単射。標的の分冪代数には正則性を課さない。

## 使われ方
Berthelot DPideal.2.3.1 の多項式の相対分冪包。Theorem 6.4 の小さい模型。
-/

public noncomputable section

universe u v

namespace SerrePositivity.BhattScholze.Prismatic.PDRelativeFree

open DividedPowerAlgebra Algebra.TensorProduct
open scoped TensorProduct

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
variable (σ : Type v) {J : Ideal A}

local notation "D" => B ⊗[A] DividedPowerAlgebra A (σ →₀ A)

/-- 自由分冪因子の生成元の像。 -/
abbrev generator (n : ℕ) (x : σ →₀ A) : D :=
  (includeRight : DividedPowerAlgebra A (σ →₀ A) →ₐ[A] D) (dp A n x)

/-- 分冪イデアルは基底イデアルの像と正次数の自由分冪で生成される。 -/
def generators (J : Ideal A) : Set D :=
  algebraMap A D '' (J : Set A) ∪ Set.range (fun (x : ℕ × (σ →₀ A)) => generator B σ (x.1 + 1) x.2)

/-- 基底イデアルと自由変数を含む分冪イデアル。 -/
abbrev ideal (J : Ideal A) : Ideal D := Ideal.span (generators B σ J)

/-- 基底の分冪イデアルの元は係数射で分冪イデアルへ入る。 -/
theorem coefficient_mem {a : A} (ha : a ∈ J) :
    algebraMap A D a ∈ ideal B σ J :=
  Ideal.subset_span (Or.inl ⟨a, ha, rfl⟩)

variable (L : Type u) [CommRing L] [Algebra B L] [Algebra A L] [IsScalarTower A B L] [Algebra ℚ L]
variable (hι : Function.Injective (algebraMap B L))
variable (γ : DividedPowers J)

local notation "M" => MvPolynomial σ L

private def evaluation : D →ₐ[A] M :=
  ((freeDPPolynomialEval σ B L).comp (freeDPBaseChangeEquiv σ A B).toAlgHom).restrictScalars A

include hι in
private theorem evaluation_injective :
    Function.Injective (evaluation (A := A) B σ L) :=
  (freeDPPolynomialEval_injective σ B L hι).comp (freeDPBaseChangeEquiv σ A B).injective

section RationalComparison

private def rationalPD (Lideal : Ideal M) : DividedPowers Lideal := by
  classical
  exact DividedPowers.RatAlgebra.dividedPowers Lideal

local notation "F" => AlgHom.toRingHom (evaluation (A := A) B σ L)
local notation "DPideal" => ideal B σ J
local notation "Irat" => Ideal.map F (Ideal.span (generators B σ J))
private def rationalStructure : DividedPowers (A := M) Irat :=
  rationalPD σ L Irat

local notation "δrat" => rationalStructure (A := A) B σ L (J := J)

private theorem mul_factorial_injective (n : ℕ) :
    Function.Injective (fun x : M => (n.factorial : M) * x) := by
  intro x y h
  exact (IsUnit.natCast_factorial_of_algebra ℚ n (A := M)).mul_left_cancel h

private theorem map_coeff_dpow (n : ℕ) {a : A} (ha : a ∈ J) :
    F (algebraMap A D (γ.dpow n a)) = (δrat).dpow n (F (algebraMap A D a)) := by
  apply mul_factorial_injective σ L n
  dsimp only
  have hm := coefficient_mem B σ ha
  rw [(δrat).factorial_mul_dpow_eq_pow (Ideal.mem_map_of_mem F hm)]
  simpa only [map_mul, map_natCast, map_pow] using
    congrArg (fun a : A => F (algebraMap A D a)) (γ.factorial_mul_dpow_eq_pow (n := n) ha)

/-- 正次数の分冪生成元は分冪イデアルに属する。 -/
theorem dp_mem (n : ℕ) (hn : n ≠ 0) (x : σ →₀ A) :
    generator B σ n x ∈ DPideal := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact Ideal.subset_span (Or.inr ⟨(m, x), rfl⟩)

private theorem map_dp (n : ℕ) (x : σ →₀ A) :
    F (generator B σ n x) = (δrat).dpow n (F (generator B σ 1 x)) := by
  apply mul_factorial_injective σ L n
  dsimp only
  rw [(δrat).factorial_mul_dpow_eq_pow (Ideal.mem_map_of_mem F (dp_mem B σ 1 one_ne_zero x))]
  simpa only [map_mul, map_natCast, map_pow] using
    congrArg (fun a : DividedPowerAlgebra A (σ →₀ A) => F ((includeRight : _ →ₐ[A] D) a))
      (DividedPowerAlgebra.natFactorial_mul_dp_eq (R := A) n x)

include γ in
private theorem lift_generator (x : D) (hx : x ∈ generators B σ J) (n : ℕ) (hn : n ≠ 0) :
    ∃ y ∈ DPideal, F y = (δrat).dpow n (F x) := by
  rcases hx with ⟨a, ha, rfl⟩ | ⟨⟨m, a⟩, rfl⟩
  · exact ⟨_, Ideal.subset_span (Or.inl ⟨_, γ.dpow_mem hn ha, rfl⟩), map_coeff_dpow B σ L γ n ha⟩
  · refine ⟨(Nat.uniformBell n (m + 1) : D) * generator B σ (n * (m + 1)) a,
      (DPideal).mul_mem_left _ (dp_mem B σ _ (mul_ne_zero hn (Nat.succ_ne_zero m)) _), ?_⟩
    rw [map_mul, map_natCast, map_dp B σ L (n * (m + 1)), map_dp B σ L (m + 1),
      (δrat).dpow_comp (Nat.succ_ne_zero m) (Ideal.mem_map_of_mem F (dp_mem B σ 1 one_ne_zero a))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- 分冪基底と自由分冪の両方を延長する構造。 -/
def dividedPowers :=
  @dividedPowersOfInjectiveSpan D M inferInstance inferInstance F (generators B σ J)
    δrat (lift_generator B σ L γ) (evaluation_injective (A := A) B σ L hι)

private theorem map_dividedPowers (n : ℕ) {x : D} (hx : x ∈ DPideal) :
    F ((dividedPowers B σ L hι γ).dpow n x) = (δrat).dpow n (F x) := by
  exact (@dividedPowersOfInjectiveSpan_isDPMorphism D M inferInstance inferInstance
    F (generators B σ J) δrat (lift_generator B σ L γ)
    (evaluation_injective (A := A) B σ L hι)).map_dpow hx

/-- 基底の分冪は係数射で保たれる。 -/
theorem base_isDPMorphism :
    γ.IsDPMorphism (dividedPowers B σ L hι γ) (algebraMap A D) := by
  have hm : ∀ a ∈ J, algebraMap A D a ∈ DPideal :=
    fun _ ha => coefficient_mem B σ ha
  refine ⟨Ideal.map_le_iff_le_comap.mpr hm, fun {n} a ha => ?_⟩
  apply evaluation_injective (A := A) B σ L hι
  exact (map_dividedPowers B σ L hι γ n (hm a ha)).trans
    (map_coeff_dpow B σ L γ n ha).symm

/-- 自由変数の一次像の分冪は自由代数の生成元。 -/
theorem dividedPowers_dp_one (n : ℕ) (x : σ →₀ A) :
    (dividedPowers B σ L hι γ).dpow n (generator B σ 1 x) = generator B σ n x := by
  apply evaluation_injective (A := A) B σ L hι
  exact (map_dividedPowers B σ L hι γ n (dp_mem B σ 1 one_ne_zero x)).trans
    (map_dp B σ L n x).symm

/-- 自由変数を分冪イデアルへ送る線形写像と係数射から、テンソル積上の代数射を作る。 -/
def lift {E : Type*} [CommRing E] [Algebra A E] {DPideal' : Ideal E} (ε : DividedPowers DPideal')
    (fB : B →ₐ[A] E) (v : (σ →₀ A) →ₗ[A] E) (hv : ∀ x, v x ∈ DPideal') : D →ₐ[A] E :=
  Algebra.TensorProduct.lift fB (DividedPowerAlgebra.lift ε v hv) (fun _ _ => Commute.all _ _)

variable {E : Type*} [CommRing E] [Algebra A E] {DPideal' : Ideal E}
variable (ε : DividedPowers DPideal') (fB : B →ₐ[A] E) (v : (σ →₀ A) →ₗ[A] E)
variable (hv : ∀ x, v x ∈ DPideal')

@[simp] theorem lift_includeLeft (b : B) :
    lift B σ ε fB v hv ((includeLeft : B →ₐ[A] D) b) = fB b :=
  DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft
    fB (DividedPowerAlgebra.lift ε v hv) (fun _ _ => Commute.all _ _)) b

@[simp] theorem lift_generator_apply (n : ℕ) (x : σ →₀ A) :
    lift B σ ε fB v hv (generator B σ n x) = ε.dpow n (v x) :=
  (DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeRight'
    fB (DividedPowerAlgebra.lift ε v hv) (fun _ _ => Commute.all _ _)) (dp A n x)).trans
    (DividedPowerAlgebra.lift_apply_dp ε hv n x)

/-- 基底の分冪と両立する標的への自由延長は分冪を保つ。 -/
theorem lift_isDPMorphism (he : γ.IsDPMorphism ε (algebraMap A E)) :
    (dividedPowers B σ L hι γ).IsDPMorphism ε (lift B σ ε fB v hv).toRingHom := by
  apply DividedPowers.IsDPMorphism.on_span _ ε (S := generators B σ J) rfl
  · rintro _ (⟨a, ha, rfl⟩ | ⟨⟨m, x⟩, rfl⟩)
    · change lift B σ ε fB v hv (algebraMap A D a) ∈ DPideal'
      rw [AlgHom.commutes]
      exact he.ideal_comp (Ideal.mem_map_of_mem _ ha)
    · change lift B σ ε fB v hv (generator B σ (m + 1) x) ∈ DPideal'
      rw [lift_generator_apply]
      exact ε.dpow_mem (Nat.succ_ne_zero _) (hv x)
  · intro n a ha
    rcases ha with ⟨a, ha, rfl⟩ | ⟨⟨m, x⟩, rfl⟩
    · have hd := (base_isDPMorphism B σ L hι γ).dpow_comp (n := n) a ha
      change lift B σ ε fB v hv ((dividedPowers B σ L hι γ).dpow n (algebraMap A D a)) = _
      rw [hd]
      change lift B σ ε fB v hv (algebraMap A D (γ.dpow n a)) =
        ε.dpow n (lift B σ ε fB v hv (algebraMap A D a))
      rw [AlgHom.commutes, AlgHom.commutes, he.dpow_comp a ha]
    · let δ := dividedPowers B σ L hι γ
      have hx := dp_mem B σ (J := J) 1 one_ne_zero x
      change lift B σ ε fB v hv (δ.dpow n (generator B σ (m + 1) x)) =
        ε.dpow n (lift B σ ε fB v hv (generator B σ (m + 1) x))
      conv_lhs => rw [← dividedPowers_dp_one B σ L hι γ (m + 1) x]
      rw [δ.dpow_comp (Nat.succ_ne_zero m) hx, dividedPowers_dp_one,
        map_mul, map_natCast, lift_generator_apply, lift_generator_apply,
        ε.dpow_comp (Nat.succ_ne_zero m) (hv x)]

end RationalComparison
end SerrePositivity.BhattScholze.Prismatic.PDRelativeFree
