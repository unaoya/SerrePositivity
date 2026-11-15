module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.IsTensorProduct

/-!
# 元の prism 剰余環の通常の係数拡大

## 概要
prism 射が主イデアルを保つ元の等式で、剰余環の通常の係数拡大を計算する。

## 方針
既存の商とテンソルの代数同型を、元のイデアルの像の等式で移す。

## 規約
平坦性・有界性・一般の HT 比較は要求しない。元の剰余射の値を保つ。

## 使われ方
特定の Zp 係数射で、通常形式の剰余係数の拡大を元の基底環の拡大へ戻す。
-/

public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q)

/-- 元の prism 剰余環の係数拡大の、終域の基底環上の標準代数同型。 -/
def prismResidueScalarTensorEquiv :
    letI := f.toRingHom.toAlgebra
    B ⊗[A] (A ⧸ P.ideal) ≃ₐ[B] B ⧸ Q.ideal := by
  letI := f.toRingHom.toAlgebra
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B P.ideal).symm.trans
    (Ideal.quotientEquivAlgOfEq B f.map_ideal_eq)

/-- この同型は、元の剰余射から来る純テンソルを指定された係数像へ送る。 -/
theorem prismResidueScalarTensorEquiv_tmul (b : B) (a : A) :
    letI := f.toRingHom.toAlgebra
    prismResidueScalarTensorEquiv f (b ⊗ₜ[A] Ideal.Quotient.mk P.ideal a) =
      Ideal.Quotient.mk Q.ideal (b * f.toRingHom a) := by
  letI := f.toRingHom.toAlgebra
  change (Ideal.quotientEquivAlgOfEq B f.map_ideal_eq)
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B P.ideal).symm
      (b ⊗ₜ[A] Ideal.Quotient.mk P.ideal a)) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change Ideal.Quotient.mk Q.ideal (a • b) = _
  change Ideal.Quotient.mk Q.ideal (f.toRingHom a * b) = _
  rw [mul_comm]

/-- 元の剰余写像は、元の基底作用のスカラーの塔を保つ。 -/
theorem prismResidueScalarTower :
    letI := f.toRingHom.toAlgebra
    letI := f.quotientMap.toAlgebra
    IsScalarTower A (A ⧸ P.ideal) (B ⧸ Q.ideal) := by
  letI := f.toRingHom.toAlgebra
  letI := f.quotientMap.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- 元の剰余環の正方形は、同じ剰余射による通常の環の押し出しである。 -/
theorem prismResidue_isPushout :
    letI := f.toRingHom.toAlgebra
    letI := f.quotientMap.toAlgebra
    letI := prismResidueScalarTower f
    Algebra.IsPushout A B (A ⧸ P.ideal) (B ⧸ Q.ideal) := by
  letI := f.toRingHom.toAlgebra
  letI := f.quotientMap.toAlgebra
  letI := prismResidueScalarTower f
  letI : Algebra (A ⧸ P.ideal) (B ⊗[A] (A ⧸ P.ideal)) :=
    Algebra.TensorProduct.rightAlgebra
  apply Algebra.IsPushout.of_equiv (prismResidueScalarTensorEquiv f)
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change prismResidueScalarTensorEquiv f ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk P.ideal a) =
    f.quotientMap (Ideal.Quotient.mk P.ideal a)
  rw [OrientedPrism.Hom.quotientMap_mk]
  simpa only [one_mul] using prismResidueScalarTensorEquiv_tmul f 1 a

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
