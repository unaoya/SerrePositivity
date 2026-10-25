module

public import SerrePositivity.BhattScholze.Andre.DividedPowerPrimeShift
public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPTruncatedAction
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# André E1・E2：分冪代数の最初の切断変数と次数シフトによるテンソル分解

## 概要

p が零となる係数環 A 上の一元分冪代数は、切断多項式環 A[X]/(Xᵖ) と
同じ分冪代数の A 上のテンソル積に同型である。
写像は c⊗d を c(γ₁) と次数シフト(d) の積に送る。
BS Rem 7.15(1)（著者版 p.62）の可算切断多項式表示の一段の分解。

## 方針

標準冪基底と分冪基底のテンソル基底が、既存の次数ブロック基底へ写ることを示す。
零係数環は両辺の自明性で扱う。

## 規約

p は素数、p=0 を係数環内の等式として明示する。係数環の非零性は要求しない。
これは通常の代数同型であり、prismatic Frobenius との同定は含まない。

## 使われ方

切断多項式評価の有限段の独立性を帰納的に示すために使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open scoped TensorProduct
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "DA" => DividedPowerAlgebra A A
local notation "C" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "hprime" => (Fact.out : p.Prime)

/-- 概要：最初の切断変数と次数シフト側の積によるテンソル評価射。
方針：切断多項式の標準評価と次数シフト代数射をテンソルの普遍性で合成する。
規約：元の係数環 A の作用を保つ。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断表示の一段の分解。 -/
def dividedPowerPrimeTensorMap (hp : (p : A) = 0) : C ⊗[A] DA →ₐ[A] DA :=
  Algebra.TensorProduct.lift (rankOneDPTruncatedMap (hprime).pos hp)
    (dividedPowerPrimeShift p hp) (fun _ _ => Commute.all _ _)

/-- 概要：テンソル評価射の純テンソル上の値は指定した二つの像の積。
方針：テンソル代数射の評価公式を使う。
規約：次数シフトは通常の Frobenius とは区別する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の基底上の計算。 -/
theorem dividedPowerPrimeTensorMap_tmul (hp : (p : A) = 0) (c : C) (d : DA) :
    dividedPowerPrimeTensorMap p hp (c ⊗ₜ[A] d) =
      rankOneDPTruncatedMap (hprime).pos hp c * dividedPowerPrimeShift p hp d := rfl

/-- 概要：テンソル評価射は零係数環を含めて全単射。
方針：非零枝ではテンソル基底を次数ブロック基底に送る線形同型と比較する。
規約：非零性は結論の前提に残さない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の可算切断表示の独立性。 -/
theorem dividedPowerPrimeTensorMap_bijective (hp : (p : A) = 0) :
    Function.Bijective (dividedPowerPrimeTensorMap (A := A) p hp) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := hA
    let : Subsingleton DA := Module.subsingleton A DA
    let : Subsingleton (C ⊗[A] DA) := Module.subsingleton A _
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  · let := hA
    let b0 := (rankOneDPTruncatedBasis p A).tensorProduct (rankOneDPAnyBasis A)
    let b1 := (rankOneDPPrimeBlockBasis hprime hp).reindex (Equiv.prodComm ℕ (Fin p))
    let e := b0.equiv b1 (Equiv.refl (Fin p × ℕ))
    have he : (dividedPowerPrimeTensorMap (A := A) p hp).toLinearMap = e.toLinearMap := by
      apply b0.ext
      rintro ⟨r, k⟩
      simp only [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
      dsimp only [e]
      rw [Module.Basis.equiv_apply]
      dsimp [b0, b1]
      rw [Module.Basis.tensorProduct_apply, Module.Basis.reindex_apply]
      change dividedPowerPrimeTensorMap p hp
        (rankOneDPTruncatedBasis p A r ⊗ₜ[A] rankOneDPAnyBasis A k) =
          rankOneDPPrimeBlockBasis hprime hp (k, r)
      rw [dividedPowerPrimeTensorMap_tmul, rankOneDPTruncatedMap_basis,
        rankOneDPAnyBasis_apply, dividedPowerPrimeShift_dp, rankOneDPPrimeBlockBasis_apply]
    change Function.Bijective (dividedPowerPrimeTensorMap (A := A) p hp).toLinearMap
    rw [he]
    exact e.bijective

/-- 概要：一元分冪代数は最初の切断多項式環と次数シフト側のテンソル積に同型。
方針：具体的な全単射代数射を代数同型として束ねる。
規約：両辺の元の A 作用を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断変数を一つずつ分ける帰納。 -/
def dividedPowerPrimeTensorEquiv (hp : (p : A) = 0) : C ⊗[A] DA ≃ₐ[A] DA :=
  AlgEquiv.ofBijective (dividedPowerPrimeTensorMap p hp) (dividedPowerPrimeTensorMap_bijective p hp)

/-- 概要：テンソル同型の順射は指定した二つの像の積を与える。
方針：全単射代数射から作った同型の台写像の等式を使う。
規約：原典の切断変数の値を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の標準射の互換性。 -/
theorem dividedPowerPrimeTensorEquiv_tmul (hp : (p : A) = 0) (c : C) (d : DA) :
    dividedPowerPrimeTensorEquiv p hp (c ⊗ₜ[A] d) =
      rankOneDPTruncatedMap (hprime).pos hp c * dividedPowerPrimeShift p hp d := rfl

end SerrePositivity.BhattScholze.Andre
