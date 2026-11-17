module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# 剰余係数の基底による係数テンソル写像の照合

## 概要
元の基底環による係数テンソル上の線形写像を、剰余係数の基底の単位純テンソルで照合する。

## 方針
剰余係数を元の環へ持ち上げ、テンソルの平衡式と有限な基底展開を使う。

## 規約
始域の基底環の作用は元の剰余写像による制限。

## 使われ方
元の通常形式の係数同型と標準 HT 写像の可換式を基底から全体へ移す。
-/

public noncomputable section
universe u v
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A)
variable {M N : Type u} [AddCommGroup M] [Module (A ⧸ I) M] [AddCommGroup N] [Module B N]
variable {ι : Type v} (b : Module.Basis ι (A ⧸ I) M)

/-- 元の係数テンソル上の線形写像は、剰余係数基底の単位純テンソル上の値で決まる。 -/
theorem residueCoefficientTensor_ext :
    letI := f.toAlgebra
    letI := Module.compHom M (Ideal.Quotient.mk I)
    ∀ (g h : B ⊗[A] M →ₗ[B] N),
      (∀ j, g ((1 : B) ⊗ₜ[A] b j) = h ((1 : B) ⊗ₜ[A] b j)) → g = h := by
  letI := f.toAlgebra
  letI := Module.compHom M (Ideal.Quotient.mk I)
  intro g h hb
  have hu (w : M) : g ((1 : B) ⊗ₜ[A] w) = h ((1 : B) ⊗ₜ[A] w) := by
    have hw := b.linearCombination_repr w
    simp only [Finsupp.linearCombination_apply, Finsupp.sum] at hw
    rw [← hw]
    simp only [TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((b.repr w) j)
    rw [← ha]
    change g ((1 : B) ⊗ₜ[A] (a • b j)) = h ((1 : B) ⊗ₜ[A] (a • b j))
    have he : ((1 : B) ⊗ₜ[A] (a • b j)) = f a • ((1 : B) ⊗ₜ[A] b j) := by
      rw [← TensorProduct.smul_tmul a (1 : B) (b j), TensorProduct.smul_tmul']
      rfl
    rw [he, map_smul, map_smul, hb]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul c w =>
    have he : c ⊗ₜ[A] w = c • ((1 : B) ⊗ₜ[A] w) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, map_smul, map_smul, hu]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
