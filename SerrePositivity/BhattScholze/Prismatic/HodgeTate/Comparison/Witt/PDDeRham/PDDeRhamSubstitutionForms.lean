module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCompletedSubstitution
public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDegree
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# 完備分冪 de Rham 形式の多項式代入

## 概要
多項式代入の Jacobian を各次数の外積に延長する。

## 方針
係数を標的に移した後、標的の係数環上で Jacobian の外積を取る。

## 規約
1 形式の基底には各頂点の変数の微分を用いる。

## 使われ方
BS 著者版 Theorem 6.4 の pd de Rham 双複体の自然性。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open SerrePositivity.KST.DerivedBlowup
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))
variable {Q Q' : Poly k} (f : Q ⟶ Q') (n : ℕ)

local notation "SourceRing" => pdTerm p k Q.n n
local notation "TargetRing" => pdTerm p k Q'.n n
local notation "SourceCopy" => ((Fin Q.n × Fin (n + 1)) →₀ k)
local notation "TargetCopy" => ((Fin Q'.n × Fin (n + 1)) →₀ k)

/-- Jacobian の各成分を完備化し、標的の係数環上へ線形に延長する。 -/
def completedJacobian : TargetRing ⊗[k] SourceCopy →ₗ[TargetRing] TargetRing ⊗[k] TargetCopy :=
  let U := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k Q'.n n))
  let u : pdRaw k Q'.n n →ₗ[k] TargetRing :=
    { toFun := U.hom
      map_add' := U.hom.map_add
      map_smul' := fun c z => by
        change U.hom (c • z) = c • U.hom z
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  ((TensorProduct.map u LinearMap.id).comp (jacobianOnCopies f n)).liftBaseChange TargetRing

/-- 任意の次数での完備分冪 de Rham 形式の多項式代入。 -/
def substituteForms (i : ℕ) : SourceRing ⊗[k] (⋀[k]^i SourceCopy) →ₗ[k] TargetRing ⊗[k] (⋀[k]^i TargetCopy) :=
  let j : TargetRing ⊗[k] (⋀[k]^i SourceCopy) →ₗ[TargetRing] TargetRing ⊗[k] (⋀[k]^i TargetCopy) :=
    (exteriorDegreeBaseChangeEquiv (R := k) (S := TargetRing) (M := TargetCopy) i).toLinearMap.comp
      ((exteriorPower.map i (completedJacobian p f n)).comp
        (exteriorDegreeBaseChangeEquiv (R := k) (S := TargetRing) (M := SourceCopy) i).symm.toLinearMap)
  (j.restrictScalars k).comp
    (TensorProduct.map (substituteCompleted p γ hk hr f n).toLinearMap LinearMap.id)

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
