module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModule
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential

/-!
# affine Hodge–Tate 写像の一次生成元

## 概要
完備一次形式の座標基底を Bockstein の像へ送る。

## 方針
基底の係数を完備多項式環へ拡大し、座標同型で係数作用をそろえる。

## 規約
dX は未完備形式からの完備化単位で表す。

## 使われ方
Hodge–Tate 写像の一次と外積への延長。
-/

public noncomputable section

open SerrePositivity.DeRham
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
  (hP : IsBoundedPrism P) (r : ℕ)

local notation "R" => affineAlgebra P r
local notation "k" => (A ⧸ P.ideal)
private abbrev oneVars (_A : Type u) (r : ℕ) : Type u := formVars r

local notation "T" => oneVars A r
local notation "B" => Poly k T
local notation "Q" => completedPoly k T p
local notation "E" => (⋀[k]^1 (T → k))
local notation "H" => hodgeTateCohomology' P hP r 1

local instance : Module R H := htModule P hP r 1

private def htOneBasis : Module.Basis T Q (Q ⊗[k] E) :=
  ((Pi.basisFun k T).map (exteriorPower.oneEquiv k (T → k)).symm).baseChange Q

private def htOneCoefficientMap :
    letI : Module Q H := Module.compHom H (affineCoordinateIso P r).symm.toRingHom
    (Q ⊗[k] E) →ₗ[Q] H := by
  let := Module.compHom H (affineCoordinateIso P r).symm.toRingHom
  exact (htOneBasis P r).constr Q fun t =>
    bockstein P hP r 0
      (hodgeTateMapZero P hP r (prismPolynomialUnit P (Fin r) (MvPolynomial.X t.down)))

private def htOneBaseChange : affineForms P r 1 ≃ₗ[Q] Q ⊗[k] E := by
  letI : IsScalarTower k B Q := completedPoly_isScalarTower k T p
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange k B Q Q E

/-- 座標の一次形式を指定された Bockstein 類へ送る線形写像。 -/
def htOneOnGenerators : affineForms P r 1 →ₗ[R] H where
  toFun x := htOneCoefficientMap P hP r (htOneBaseChange P r x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by
    let := Module.compHom H (affineCoordinateIso P r).symm.toRingHom
    change htOneCoefficientMap P hP r (htOneBaseChange P r (affineCoordinateIso P r a • x)) = _
    rw [map_smul, map_smul]
    change (affineCoordinateIso P r).symm (affineCoordinateIso P r a) •
      htOneCoefficientMap P hP r (htOneBaseChange P r x) = _
    rw [RingEquiv.symm_apply_apply, RingHom.id_apply]

/-- 完備化した座標一次形式。 -/
def affineCoordinateFormOne (t : Fin r) : affineForms P r 1 :=
  completedFormsUnit k T p 1
    (1 ⊗ₜ[k] (exteriorPower.oneEquiv k (T → k)).symm (Pi.single (ULift.up t) 1))

/-- 各座標の一次形式で、係数線形写像は Bockstein を与える。 -/
theorem htOneOnGenerators_coordinate (t : Fin r) :
    htOneOnGenerators P hP r (affineCoordinateFormOne P r t) =
      bockstein P hP r 0 (hodgeTateMapZero P hP r
        (prismPolynomialUnit P (Fin r) (MvPolynomial.X t))) := by
  change htOneCoefficientMap P hP r (htOneBaseChange P r (affineCoordinateFormOne P r t)) = _
  have h : htOneBaseChange P r (affineCoordinateFormOne P r t) =
      htOneBasis P r (ULift.up t) := by
    rw [affineCoordinateFormOne]
    change completedFormsCoeffEquiv k T p 1 (completedFormsUnit k T p 1 (1 ⊗ₜ[k] _)) = _
    rw [completedFormsCoeffEquiv_unit_tmul, map_one]
    simp [htOneBasis, Module.Basis.baseChange_apply, Pi.basisFun_apply]
    rfl
  rw [h, htOneCoefficientMap, Module.Basis.constr_basis]

end SerrePositivity.BhattScholze.Prismatic
