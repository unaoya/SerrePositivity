module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# 自由変数の分冪代数と係数拡大

## 概要
自由加群上の分冪代数を有限台の分冪単項式で生成し、係数拡大の標準射を定める。

## 方針
Mathlib の分冪代数の関手性と有限台基底を使う。

## 規約
変数集合は任意で、各単項式の台は有限。

## 使われ方
結晶の橋と、Čech–Alexander 模型に現れる分冪座標。
-/

@[expose] public section
noncomputable section

universe u v w

open scoped TensorProduct

namespace SerrePositivity.BhattScholze

variable (S : Type w) (A : Type u) [CommRing A]

/-- 有限台の指数で添字付けた自由分冪単項式。 -/
def freeDPMonomial (m : S →₀ ℕ) : DividedPowerAlgebra A (S →₀ A) :=
  m.prod fun s n => DividedPowerAlgebra.dp A n (Finsupp.single s 1)

/-- 自由分冪代数は分冪単項式で加群として生成される。 -/
theorem freeDPMonomial_span : Submodule.span A (Set.range (freeDPMonomial S A)) = ⊤ :=
  DividedPowerAlgebra.submodule_span_prod_dp_eq_top (Finsupp.basisSingleOne (R := A) (ι := S)).span_eq

variable (B : Type v) [CommRing B] [Algebra A B]

/-- 自由加群の係数を拡大する線形写像。 -/
def freeDPCoefficientMap : (S →₀ A) →ₗ[A] (S →₀ B) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap A B)

/-- 概要：自由分冪代数の係数拡大の標準射。
方針：テンソル積の普遍性と分冪代数の関手性。
規約：単項式の変数集合は係数拡大の前後で同じ。
使われ方：多変数の分冪包の係数比較。 -/
def freeDPBaseChangeMap :
    B ⊗[A] DividedPowerAlgebra A (S →₀ A) →ₐ[B] DividedPowerAlgebra B (S →₀ B) :=
  Algebra.TensorProduct.lift (Algebra.ofId B (DividedPowerAlgebra B (S →₀ B)))
    (DividedPowerAlgebra.map B (freeDPCoefficientMap S A B)) (fun _ _ => Commute.all _ _)

/-- 自由分冪単項式は係数拡大の前後で対応する。 -/
theorem freeDPBaseChangeMap_monomial (m : S →₀ ℕ) :
    freeDPBaseChangeMap S A B (1 ⊗ₜ[A] freeDPMonomial S A m) = freeDPMonomial S B m := by
  change algebraMap B _ 1 *
    DividedPowerAlgebra.map B (freeDPCoefficientMap S A B) (freeDPMonomial S A m) = _
  rw [map_one, one_mul]
  unfold freeDPMonomial Finsupp.prod
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s _
  rw [DividedPowerAlgebra.map_apply_dp]
  congr 1
  ext j
  by_cases h : s = j
  · subst j
    simp [freeDPCoefficientMap]
  · simp [freeDPCoefficientMap, Finsupp.single_eq_of_ne (Ne.symm h)]

/-- 自由分冪代数の係数拡大の標準射は全射。 -/
theorem freeDPBaseChangeMap_surjective : Function.Surjective (freeDPBaseChangeMap S A B) := by
  change Function.Surjective (freeDPBaseChangeMap S A B).toLinearMap
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← freeDPMonomial_span S B, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact ⟨1 ⊗ₜ[A] freeDPMonomial S A m, freeDPBaseChangeMap_monomial S A B m⟩

end SerrePositivity.BhattScholze
