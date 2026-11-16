module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# 元の affine 完備形式の有限自由性と射影性

## 概要
元の完備形式は、元の affine 係数環上で有限自由かつ射影である。

## 方針
元の関数加群の外冪基底を係数拡大し、テンソルの結合と元の座標同型で戻す。

## 規約
元の affineFormsModule の作用を使う。基底環を Zp や体へ制限しない。

## 使われ方
元の標準 HT コホモロジー写像を、元の複体への射として実現する。
-/

public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.DeRham CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (r : ℕ)
local notation "k" => A ⧸ P.ideal
private abbrev affineProjectiveVars (_A : Type u) (r : ℕ) : Type u := formVars r
local notation "T" => affineProjectiveVars A r
local notation "B" => Poly k T
local notation "Q" => completedPoly k T p

private def affineCompletedFormsBasis (i : ℕ) :
    Module.Basis (Set.powersetCard T i) (affineAlgebra P r) (affineForms P r i) := by
  letI := completedPoly_isScalarTower k T p
  let E := ⋀[k]^i (T → k)
  let e : affineForms P r i ≃ₗ[Q] Q ⊗[k] E :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange k B Q Q E
  let b := (((Pi.basisFun k T).exteriorPower i).baseChange Q).map e.symm
  exact b.mapCoeffs (affineCoordinateIso P r).symm (fun q w => by
    change affineCoordinateIso P r ((affineCoordinateIso P r).symm q) • w = q • w
    rw [RingEquiv.apply_symm_apply])

/-- 元の affine 係数作用に関する完備形式の自由性。 -/
theorem affineForms_free (i : ℕ) : Module.Free (affineAlgebra P r) (affineForms P r i) :=
  Module.Free.of_basis (affineCompletedFormsBasis P r i)

/-- 元の affine 係数作用に関する完備形式の有限性。 -/
theorem affineForms_finite (i : ℕ) : Module.Finite (affineAlgebra P r) (affineForms P r i) :=
  Module.Finite.of_basis (affineCompletedFormsBasis P r i)

/-- 元の完備形式は、元の係数加群の圏でも射影対象。 -/
theorem affineForms_projective (i : ℕ) :
    Projective (ModuleCat.of (affineAlgebra P r) (affineForms P r i)) := by
  exact ModuleCat.projective_of_free (affineCompletedFormsBasis P r i)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
