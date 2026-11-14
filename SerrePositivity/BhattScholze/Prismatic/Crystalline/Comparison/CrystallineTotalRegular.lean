module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBockstein
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
public import SerrePositivity.HomologicalAlgebra.BicomplexComponents
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBockstein
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# 整係数の pd de Rham 総複体の p 正則性

## 概要
整係数の完備 pd 形式とその総複体に p ねじれがない。

## 方針
外冪の座標基底で各項を完備 pd 環の自由加群として読み、総複体では各成分で判定する。

## 規約
係数環は結晶基底の整係数環。

## 使われ方
Bockstein の持ち上げの微分を p で割った余輪体。
-/

public noncomputable section

open CategoryTheory SerrePositivity.HomologicalAlgebra
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "K" => crystallineBase p

set_option backward.isDefEq.respectTransparency false in
private theorem pdForms_p_regular (n : SimplexCategory) (j : ℕ)
    (x : (pdRow p (crystallineBase.{u} p) r j).obj n) (hx : (p : K) • x = 0) : x = 0 := by
  classical
  let S : Type u := pdTerm p (crystallineBase.{u} p) r n.len
  let I := Fin r × Fin (n.len+1)
  let e := Fintype.equivFin I
  let : LinearOrder I := LinearOrder.lift' e e.injective
  let b := (Finsupp.basisSingleOne (R := crystallineBase.{u} p) (ι := I)).exteriorPower j
  let c := b.baseChange S
  change S ⊗[K] (⋀[K]^j (I →₀ K)) at x
  have h : (p : S) • x = 0 := by
    rw [← map_natCast (algebraMap K S), algebraMap_smul]
    exact hx
  apply c.repr.injective
  ext i
  apply pdRings_p_regular p r n
  have hi := congrArg (fun z => c.repr z i) h
  simpa only [map_smul, map_zero, Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul, mul_zero] using hi

set_option backward.isDefEq.respectTransparency false in
/-- 整係数の pd de Rham 総複体の各項で、p 倍が零なら元が零。 -/
theorem pdTotal_eq_zero_of_p_smul (n : ℕ)
    (x : (pdDeRhamTotal p (crystallineBase.{u} p) r).X n)
    (hx : (p : K) • x = 0) : x = 0 := by
  let L := pdDeRhamDoubleComplex p (crystallineBase.{u} p) r
  apply totalComponent_ext_zero L
  intro a b hab
  let f := componentAt L n ⟨(a,b),hab⟩
  apply pdForms_p_regular p r ⦋a⦌ b
  change (p : K) • f x = 0
  rw [← map_smul, hx, map_zero]

end SerrePositivity.BhattScholze.Prismatic
