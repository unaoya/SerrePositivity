module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModuleComplete
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneGenerators
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap

/-!
# affine Hodge–Tate の零次の導分

## 概要
係数からの Bockstein と完備 de Rham 微分を比較する。

## 方針
完備化の一意性により多項式に戻し、導分を座標ごとに計算する。

## 規約
係数の作用は零次からの左 cup 積。

## 使われ方
affine Hodge–Tate 写像の一次。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham
  SerrePositivity.DerivedCompletion MvPolynomial
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
  (hP : IsBoundedPrism P) (r : ℕ)

local notation "k" => A ⧸ P.ideal
local notation "T" => oneVars A r
local notation "B" => Poly k T
local notation "Q" => completedPoly k T p
local notation "R" => affineAlgebra P r
local notation "H" => hodgeTateCohomology' P hP r 1
local notation "E₀" => (⋀[k]^0 (T → k))
local notation "E₁" => (⋀[k]^1 (T → k))

local instance : Module R H := htModule P hP r 1
local instance : Module k H := Module.compHom H (algebraMap k R)

private abbrev e := affineCoordinateIso P r

private theorem coord_map_C (a : k) : e P r (algebraMap k R a) = algebraMap k Q a := by
  let f := MvPolynomial.renameEquiv k (Equiv.ulift.symm : Fin r ≃ formVars.{u} r)
  have h := ConcreteCategory.congr_hom
    (ringCatMap_comp_unit p f.toRingEquiv.toCommRingCatIso.hom) (MvPolynomial.C a)
  exact h.trans (congrArg (algebraMap B Q) (MvPolynomial.rename_C _ _))

private theorem coord_symm_map_C (a : k) :
    (e P r).symm (algebraMap k Q a) = algebraMap k R a :=
  (e P r).symm_apply_eq.mpr (coord_map_C P r a).symm

private def transferredBockstein : Q →ₗ[k] H where
  toAddHom := (htBocksteinZero P hP r).comp (e P r).symm.toAddMonoidHom
  map_smul' a f := by
    change htBocksteinZero P hP r ((e P r).symm ((algebraMap k Q a) * f)) =
      (algebraMap k R a) • htBocksteinZero P hP r ((e P r).symm f)
    rw [map_mul, coord_symm_map_C, htBocksteinZero_mul, htBocksteinZero_algebraMap,
      smul_zero, add_zero]

private theorem transferredBockstein_C (a : k) :
    transferredBockstein P hP r (algebraMap k Q a) = 0 := by
  change htBocksteinZero P hP r ((e P r).symm (algebraMap k Q a)) = 0
  rw [coord_symm_map_C, htBocksteinZero_algebraMap]

private theorem transferredBockstein_mul (f g : Q) :
    transferredBockstein P hP r (f * g) =
      (e P r).symm f • transferredBockstein P hP r g +
        (e P r).symm g • transferredBockstein P hP r f := by
  change htBocksteinZero P hP r ((e P r).symm (f * g)) =
    (e P r).symm f • htBocksteinZero P hP r ((e P r).symm g) +
      (e P r).symm g • htBocksteinZero P hP r ((e P r).symm f)
  rw [map_mul, htBocksteinZero_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem htOneD_value (f : R) :
    htOneOnGenerators P hP r (affineD P r 0 (degreeZeroForm P r f)) =
      ∑ t : T, (e P r).symm (completedPderiv k T p t (e P r f)) •
        htBocksteinZero P hP r (prismPolynomialUnit P (Fin r) (MvPolynomial.X t.down)) := by
  let := completedPoly_isScalarTower k T p
  let := Module.compHom H (e P r).symm.toRingHom
  let one : E₀ := (exteriorPower.zeroEquiv k (T → k)).symm 1
  have h₀ : completedFormsCoeffEquiv k T p 0 (degreeZeroForm P r f) = e P r f ⊗ₜ[k] one := by
    change TensorProduct.AlgebraTensorModule.cancelBaseChange k B Q Q E₀
      (e P r f ⊗ₜ[B] (formsZeroEquiv k T 1)) = _
    rw [formsZeroEquiv_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      Algebra.smul_def, map_one, one_mul]
  have h (t : T) : wedgeOne k (T → k) 0
      ((exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1)) one =
      (exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1) := by
    apply Subtype.ext
    simp [wedgeOne, exteriorWedge, one, exteriorPower.zeroEquiv, exteriorPower.oneEquiv_symm_apply,
      ExteriorAlgebra.ιMulti_apply]
  change htOneCoefficientMap P hP r (completedFormsCoeffEquiv k T p 1
    (affineD P r 0 (degreeZeroForm P r f))) = _
  rw [completedFormsCoeffEquiv_d, h₀]
  erw [rawD, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [TensorProduct.map_tmul, h]
  let a := completedPderiv k T p t (e P r f)
  have hB : a ⊗ₜ[k] (exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1) =
      a • htOneBasis P r t := by
    simp [htOneBasis, Module.Basis.baseChange_apply, Pi.basisFun_apply, a]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hB, map_smul, htOneCoefficientMap, Module.Basis.constr_basis]
  rfl

local instance : IsScalarTower k R H := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private def bocksteinCoordinate (t : T) : H :=
  htBocksteinZero P hP r (prismPolynomialUnit P (Fin r) (MvPolynomial.X t.down))

private def completedDerivativeTerm (t : T) : Q →ₗ[k] H where
  toFun q := (e P r).symm (completedPderiv k T p t q) • bocksteinCoordinate P hP r t
  map_add' x y := by simp [map_add, add_smul]
  map_smul' a q := by
    rw [map_smul]
    change (e P r).symm ((algebraMap k Q a) * completedPderiv k T p t q) •
      bocksteinCoordinate P hP r t = _
    rw [map_mul, coord_symm_map_C, mul_smul]
    rfl

private def completedDerivative : Q →ₗ[k] H :=
  ∑ t : T, completedDerivativeTerm P hP r t

private theorem completedDerivative_apply (f : Q) :
    completedDerivative P hP r f =
      ∑ t : T, (e P r).symm (completedPderiv k T p t f) • bocksteinCoordinate P hP r t := by
  rw [completedDerivative, LinearMap.sum_apply]
  rfl

private theorem rawDerivative_apply (f : B) :
    completedDerivative P hP r (algebraMap B Q f) =
      ∑ t : T, (e P r).symm (algebraMap B Q (pderiv t f)) • bocksteinCoordinate P hP r t := by
  rw [completedDerivative_apply]
  simp only [completedPderiv_unit]

set_option maxHeartbeats 900000 in
-- 完備係数作用と未完備偏微分の積公式を照合する。
private theorem rawDerivative_mul (f g : B) :
    completedDerivative P hP r (algebraMap B Q (f*g)) =
      (e P r).symm (algebraMap B Q f) • completedDerivative P hP r (algebraMap B Q g) +
      (e P r).symm (algebraMap B Q g) • completedDerivative P hP r (algebraMap B Q f) := by
  have h (t : T) : pderiv t (f*g) = g * pderiv t f + f * pderiv t g := by
    rw [pderiv_mul, mul_comm (pderiv t f) g]
  rw [rawDerivative_apply, rawDerivative_apply, rawDerivative_apply, Finset.smul_sum,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  erw [h t, map_add, map_add, add_smul, map_mul, map_mul, map_mul, map_mul, mul_smul, mul_smul]
  exact add_comm _ _

private theorem rawDerivative_X (t : T) :
    completedDerivative P hP r (algebraMap B Q (MvPolynomial.X t)) =
      bocksteinCoordinate P hP r t := by
  rw [rawDerivative_apply, Finset.sum_eq_single t]
  · rw [pderiv_X_self, map_one, map_one, one_smul]
  · intro s _ hs
    rw [pderiv_X_of_ne hs.symm, map_zero, map_zero, zero_smul]
  · simp

private theorem transferredBockstein_unit (f : B) :
    transferredBockstein P hP r (algebraMap B Q f) =
      completedDerivative P hP r (algebraMap B Q f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [rawDerivative_apply]
    change transferredBockstein P hP r (algebraMap k Q a) = _
    rw [transferredBockstein_C]
    simp only [pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f t hf =>
    rw [rawDerivative_mul, map_mul, transferredBockstein_mul, ← hf, rawDerivative_X]
    congr 2
    have h := affineCoordinateIso_X P r t.down
    change e P r (prismPolynomialUnit P (Fin r) (MvPolynomial.X t.down)) =
      algebraMap B Q (MvPolynomial.X t) at h
    exact congrArg (htBocksteinZero P hP r) ((e P r).symm_apply_eq.mpr h.symm)

private theorem transferredBockstein_eq :
    transferredBockstein P hP r = completedDerivative P hP r := by
  have hc : IsModuleComplete k (p : k) (ModuleCat.of k H) :=
    (isModuleComplete_algebraMap_iff k R (p : k) H).mp (by
      rw [map_natCast]
      exact htModule_isModuleComplete P hP r 1)
  apply principalCompletionLinearMap_ext k p hc
  intro f
  exact transferredBockstein_unit P hP r f

/-- 零次係数の完備微分を一次の Hodge–Tate 写像に入れると Bockstein を得る。 -/
theorem htOneOnGenerators_d (f : R) :
    htOneOnGenerators P hP r (affineD P r 0 (degreeZeroForm P r f)) =
      htBocksteinZero P hP r f := by
  rw [htOneD_value]
  change (∑ t : T, (e P r).symm (completedPderiv k T p t (e P r f)) •
    bocksteinCoordinate P hP r t) = _
  rw [← completedDerivative_apply, ← transferredBockstein_eq]
  rw [show transferredBockstein P hP r (e P r f) =
    htBocksteinZero P hP r ((e P r).symm (e P r f)) from rfl, RingEquiv.symm_apply_apply]

/-- 一次の Hodge–Tate 写像。 -/
def hodgeTateMapOne : affineForms P r 1 →ₗ[R] H :=
  htOneOnGenerators P hP r

/-- 一次の Hodge–Tate 写像と、零次係数の微分での値。 -/
theorem hodgeTateMapOne_smul_d (f g : R) :
    hodgeTateMapOne P hP r (f • affineD P r 0 (degreeZeroForm P r g)) =
      f • htBocksteinZero P hP r g := by
  rw [map_smul, hodgeTateMapOne, htOneOnGenerators_d]

end SerrePositivity.BhattScholze.Prismatic
