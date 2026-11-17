module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# 係数像が同伴なスカラーの商と元のテンソル比較

## 概要
係数拡大先で同伴になる二つの基底スカラーによる商は、元の純テンソルを保って一致する。

## 方針
元のテンソルの左右の係数脚の可換式で拡大イデアルを比較し、既存の商テンソル同型を使う。

## 規約
平坦性も整域性も仮定しない。純テンソル上で元の代表元を保持する。

## 使われ方
α(d)=p*u のもとで、元の剰余行を既存の結晶剰余項の比較へ移す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- 係数像が同伴なら、二つのスカラーのイデアルは元のテンソル環で一致する。 -/
theorem tensorScalarIdeal_eq (φ : A →+* B) (ψ : A →+* C) (a b : A)
    (h : Associated (φ a) (φ b)) :
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    (Ideal.span {ψ a}).map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom =
      (Ideal.span {ψ b}).map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  let l : B →+* B ⊗[A] C := Algebra.TensorProduct.includeLeftRingHom
  let r : C →+* B ⊗[A] C := Algebra.TensorProduct.includeRight.toRingHom
  have he (x : A) : r (ψ x) = l (φ x) :=
    (RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := A) (A := B) (B := C)) x).symm
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  change Ideal.span {r (ψ a)} = Ideal.span {r (ψ b)}
  rw [he, he]
  have hh := Associated.map l h
  apply le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hh.dvd'
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hh.dvd

/-- 元の基底スカラーの商の係数拡大は、その像が同伴なら指定された代数同型を持つ。 -/
def tensorScalarQuotientEquiv (φ : A →+* B) (ψ : A →+* C) (a b : A)
    (h : Associated (φ a) (φ b)) :
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    B ⊗[A] (C ⧸ Ideal.span {ψ a}) ≃ₐ[B] B ⊗[A] (C ⧸ Ideal.span {ψ b}) := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B C B (Ideal.span {ψ a})).trans
    ((Ideal.quotientEquivAlgOfEq B (tensorScalarIdeal_eq φ ψ a b h)).trans
      (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B C B (Ideal.span {ψ b})).symm)

/-- 指定された商のテンソル比較は、元の純テンソルの代表元を保つ。 -/
theorem tensorScalarQuotientEquiv_tmul (φ : A →+* B) (ψ : A →+* C) (a b : A)
    (h : Associated (φ a) (φ b)) (y : B) (z : C) :
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    tensorScalarQuotientEquiv φ ψ a b h (y ⊗ₜ[A] Ideal.Quotient.mk _ z) =
      y ⊗ₜ[A] Ideal.Quotient.mk _ z := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  simp only [tensorScalarQuotientEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  erw [Ideal.quotientEquivAlgOfEq_mk]
  exact Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul
    (R := A) B C B (Ideal.span {ψ b}) y z

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
