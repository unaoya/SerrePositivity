module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDP
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# 自由分冪代数の係数拡大同型

## 概要
任意個の自由変数を持つ分冪代数の係数拡大について、標準射の逆を作る。

## 方針
一変数ごとの分冪を係数とする形式的冪級数を有限個掛け合わせる。
分冪の積の関係は、二変数への代入と乗法の両立から従う。

## 規約
級数の変数は分冪の次数を記録する。自由加群の各元の台は有限。

## 使われ方
多変数の分冪包の係数比較。
-/

public section
noncomputable section

universe u v w

open scoped TensorProduct PowerSeries
open Finset

namespace SerrePositivity.BhattScholze

section Series

variable {R : Type*} [CommRing R]

private def IsDPSeries (f : R⟦X⟧) : Prop :=
  f.constantCoeff = 1 ∧
    f.subst (MvPowerSeries.X (R := R) (0 : Fin 2) + MvPowerSeries.X (R := R) (1 : Fin 2)) =
      f.subst (MvPowerSeries.X (R := R) (0 : Fin 2)) * f.subst (MvPowerSeries.X (R := R) (1 : Fin 2))

private theorem isDPSeries_iff (f : R⟦X⟧) : IsDPSeries f ↔
    PowerSeries.coeff 0 f = 1 ∧ ∀ m n : ℕ,
      PowerSeries.coeff m f * PowerSeries.coeff n f =
        (m + n).choose m • PowerSeries.coeff (m + n) f := by
  rw [IsDPSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  apply and_congr_right
  intro _
  constructor
  · intro h m n
    have hc := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 n)) h
    rw [PowerSeries.coeff_subst_X_zero_add_X_one,
      PowerSeries.coeff_subst_X_zero_subst_mul_X_one] at hc
    simpa [nsmul_eq_mul] using hc.symm
  · intro h
    apply MvPowerSeries.ext
    intro e
    rw [PowerSeries.coeff_subst_X_zero_add_X_one,
      PowerSeries.coeff_subst_X_zero_subst_mul_X_one, h (e 0) (e 1), nsmul_eq_mul]

private theorem isDPSeries_mul {f g : R⟦X⟧} (hf : IsDPSeries f) (hg : IsDPSeries g) :
    IsDPSeries (f * g) := by
  obtain ⟨h₀f, hf⟩ := hf
  obtain ⟨h₀g, hg⟩ := hg
  refine ⟨by simp [h₀f, h₀g], ?_⟩
  let X₀ : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0
  let X₁ : MvPowerSeries (Fin 2) R := MvPowerSeries.X 1
  have h₀ : PowerSeries.HasSubst X₀ := PowerSeries.HasSubst.X 0
  have h₁ : PowerSeries.HasSubst X₁ := PowerSeries.HasSubst.X 1
  have hs : PowerSeries.HasSubst (X₀ + X₁) := h₀.add h₁
  change (f * g).subst (X₀ + X₁) = (f * g).subst X₀ * (f * g).subst X₁
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_mul h₀, PowerSeries.subst_mul h₁]
  change f.subst (X₀ + X₁) = _ at hf
  change g.subst (X₀ + X₁) = _ at hg
  rw [hf, hg]
  ac_rfl

private theorem isDPSeries_one : IsDPSeries (1 : R⟦X⟧) := by
  rw [isDPSeries_iff]
  refine ⟨by simp, ?_⟩
  intro m n
  cases m <;> cases n <;> simp [PowerSeries.coeff_one]

end Series

variable {S : Type w} {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

local notation "D" => B ⊗[A] DividedPowerAlgebra A (S →₀ A)

private def dpScalarSeries (s : S) (b : B) : D⟦X⟧ :=
  PowerSeries.mk fun n => (b ^ n) ⊗ₜ[A] DividedPowerAlgebra.dp A n (Finsupp.single s 1)

@[local simp] private theorem dpScalarSeries_coeff (s : S) (b : B) (n : ℕ) :
    PowerSeries.coeff n (dpScalarSeries (A := A) s b) =
      (b ^ n) ⊗ₜ[A] DividedPowerAlgebra.dp A n (Finsupp.single s 1) :=
  PowerSeries.coeff_mk _ _

private theorem dpScalarSeries_zero (s : S) : dpScalarSeries (A := A) s (0 : B) = 1 := by
  ext n
  cases n
  · simp [PowerSeries.coeff_one, DividedPowerAlgebra.dp_zero, Algebra.TensorProduct.one_def]
  · simp [PowerSeries.coeff_one]

private theorem isDPSeries_dpScalarSeries (s : S) (b : B) :
    IsDPSeries (dpScalarSeries (A := A) s b) := by
  rw [isDPSeries_iff]
  simp only [dpScalarSeries_coeff, pow_zero, DividedPowerAlgebra.dp_zero]
  refine ⟨Algebra.TensorProduct.one_def.symm, fun n m => ?_⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← pow_add, DividedPowerAlgebra.dp_mul,
    TensorProduct.tmul_smul]

private theorem dpScalarSeries_add (s : S) (b c : B) :
    dpScalarSeries (A := A) s (b + c) =
      dpScalarSeries (A := A) s b * dpScalarSeries (A := A) s c := by
  ext n
  rw [PowerSeries.coeff_mul, dpScalarSeries_coeff, (Commute.all b c).add_pow',
    TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [dpScalarSeries_coeff]
  have hn : k.1 + k.2 = n := Finset.mem_antidiagonal.mp hk
  rw [Algebra.TensorProduct.tmul_mul_tmul, DividedPowerAlgebra.dp_mul, hn, TensorProduct.tmul_smul]
  exact (TensorProduct.smul_tmul' (n.choose k.1) (b ^ k.1 * c ^ k.2)
    (DividedPowerAlgebra.dp A n (Finsupp.single s 1))).symm

private theorem dpScalarSeries_smul (s : S) (b c : B) :
    dpScalarSeries (A := A) s (b * c) =
      PowerSeries.rescale (algebraMap B D b) (dpScalarSeries (A := A) s c) := by
  ext n
  rw [PowerSeries.coeff_rescale]
  simp only [dpScalarSeries_coeff, mul_pow, ← map_pow, ← Algebra.smul_def, TensorProduct.smul_tmul']
  rfl

private def freeDPSeries (b : S →₀ B) : D⟦X⟧ :=
  b.prod (dpScalarSeries (A := A))

private theorem isDPSeries_freeDPSeries (b : S →₀ B) :
    IsDPSeries (freeDPSeries (A := A) b) :=
  Finset.prod_induction _ IsDPSeries (fun _ _ => isDPSeries_mul)
    isDPSeries_one fun s _ => isDPSeries_dpScalarSeries s (b s)

private theorem freeDPSeries_add (b c : S →₀ B) :
    freeDPSeries (A := A) (b + c) = freeDPSeries (A := A) b * freeDPSeries (A := A) c :=
  Finsupp.prod_add_index' dpScalarSeries_zero dpScalarSeries_add

private theorem freeDPSeries_smul (c : B) (b : S →₀ B) :
    freeDPSeries (A := A) (c • b) =
      PowerSeries.rescale (algebraMap B D c) (freeDPSeries (A := A) b) := by
  classical
  unfold freeDPSeries
  rw [Finsupp.prod_of_support_subset (c • b) Finsupp.support_smul _ (fun s _ => dpScalarSeries_zero s)]
  rw [Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro s _
  rw [Finsupp.smul_apply, smul_eq_mul, dpScalarSeries_smul]

/-- 概要：自由分冪代数の係数拡大の標準射に対する逆射。
方針：分冪の像を、変数ごとの分冪級数の有限積の係数で定める。
規約：分冪代数の係数環にねじれを許す。
使われ方：分冪単項式での係数拡大同型。 -/
def freeDPBaseChangeInverse : DividedPowerAlgebra B (S →₀ B) →ₐ[B] D :=
  DividedPowerAlgebra.lift'
    (f := fun nb => PowerSeries.coeff nb.1 (freeDPSeries (A := A) nb.2))
    (fun b => ((isDPSeries_iff _).mp (isDPSeries_freeDPSeries b)).1)
    (fun n c b => by
      rw [freeDPSeries_smul, PowerSeries.coeff_rescale, ← map_pow, ← Algebra.smul_def])
    (fun n m b => ((isDPSeries_iff _).mp (isDPSeries_freeDPSeries b)).2 n m)
    (fun n b c => by rw [freeDPSeries_add, PowerSeries.coeff_mul])

/-- 逆射は分冪単項式を係数 1 の純テンソルに写す。 -/
theorem freeDPBaseChangeInverse_monomial (m : S →₀ ℕ) :
    freeDPBaseChangeInverse (A := A) (freeDPMonomial S B m) =
      (1 : B) ⊗ₜ[A] freeDPMonomial S A m := by
  unfold freeDPMonomial Finsupp.prod
  let j : DividedPowerAlgebra A (S →₀ A) →ₐ[A] D := Algebra.TensorProduct.includeRight
  change _ = j _
  rw [map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro s _
  rw [freeDPBaseChangeInverse, DividedPowerAlgebra.lift'_apply_dp]
  simp only [freeDPSeries, Finsupp.prod_single_index (dpScalarSeries_zero s), dpScalarSeries_coeff,
    one_pow]
  rfl

private theorem freeDPBaseChange_leftInverse :
    Function.LeftInverse (freeDPBaseChangeInverse (S := S) (A := A) (B := B))
      (freeDPBaseChangeMap S A B) := by
  let f := (freeDPBaseChangeInverse (S := S) (A := A) (B := B)).comp (freeDPBaseChangeMap S A B)
  have hf : f = AlgHom.id B D := by
    apply Algebra.TensorProduct.ext
    · ext
    · apply AlgHom.toLinearMap_injective
      rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (freeDPMonomial_span S A)]
      rintro ⟨_, m, rfl⟩
      change freeDPBaseChangeInverse (A := A)
        (freeDPBaseChangeMap S A B (1 ⊗ₜ[A] freeDPMonomial S A m)) =
          (1 : B) ⊗ₜ[A] freeDPMonomial S A m
      rw [freeDPBaseChangeMap_monomial, freeDPBaseChangeInverse_monomial]
  intro z
  exact DFunLike.congr_fun hf z

/-- 概要：任意個の自由変数を持つ分冪代数の係数拡大同型。
方針：標準射の全射性と、分冪級数から得た左逆射を使う。
規約：係数拡大は任意の可換環の代数射に沿う。
使われ方：多変数分冪包の係数比較。 -/
def freeDPBaseChangeEquiv (S : Type w) (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] DividedPowerAlgebra A (S →₀ A) ≃ₐ[B] DividedPowerAlgebra B (S →₀ B) :=
  AlgEquiv.ofBijective (freeDPBaseChangeMap S A B)
    ⟨freeDPBaseChange_leftInverse.injective, freeDPBaseChangeMap_surjective S A B⟩

/-- 係数拡大同型の順射は標準射。 -/
@[simp]
theorem freeDPBaseChangeEquiv_apply (z : D) :
    freeDPBaseChangeEquiv S A B z = freeDPBaseChangeMap S A B z := by
  unfold freeDPBaseChangeEquiv
  rfl

end SerrePositivity.BhattScholze
