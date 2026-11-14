module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCohomology
public import SerrePositivity.HomologicalAlgebra.CochainProductNaturality
import all SerrePositivity.HomologicalAlgebra.CochainProductNaturality
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCohomology
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives

/-!
# 余輪体の代表による pd de Rham 比較

## 概要
総複体の一つの余輪体を二つの射影で写して得られる比較の値を与える。

## 方針
二つの射影の擬同型と、余鎖写像による閉余鎖の類の自然性を使う。

## 規約
横の代表は余単体的環の交代余面複体で、縦の代表は通常の多項式形式で読む。

## 使われ方
結晶基底の Frobenius 座標と一次 Cartier 類の照合。
-/

public noncomputable section

open CategoryTheory HomologicalComplex SerrePositivity.Cosimplicial SerrePositivity.DeRham
open SerrePositivity.HomologicalAlgebra.CochainProduct
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) (hp : (p : k) = 0)

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
/-- 二つの射影で一致する余輪体の代表を、比較同型が対応させる。 -/
theorem pdDeRhamCechToPolynomial_class (i : ℕ) (x : (pdDeRhamTotal p k r).X i)
    (hx : (pdDeRhamTotal p k r).d i (i+1) x = 0)
    (a : Cocycles (pdCechRings p k r) i) (ω : forms k (formVars.{u} r) i)
    (hω : deRhamD k (formVars.{u} r) i ω = 0)
    (ha : (pdDeRhamRowZeroIso p k r).hom.f i ((pdDeRhamRowZeroProjection p k r).f i x) = a.1)
    (hb : (pdDeRhamColumnZeroIso k r p hp).hom.f i ((pdDeRhamColumnZeroProjection p k r).f i x) =
      deRhamTerm k (formVars.{u} r) i ω) :
    pdDeRhamCechToPolynomial p k r hp i (cohomologyClass _ i a) =
      deRhamClass k (formVars.{u} r) i ω hω := by
  let E := pdDeRhamTotalToCech p k r i
  let D := cohomologyEquivModuleHomology k (pdCechRings p k r) (pdCechBase p k r) i
  let f := pdDeRhamRowZeroProjection p k r
  let g := (pdDeRhamRowZeroIso p k r).hom
  let h := pdDeRhamColumnZeroProjection p k r
  let l := (pdDeRhamColumnZeroIso k r p hp).hom
  let z := closedClass i x hx
  have hE : E z = cohomologyClass _ i a := by
    apply D.injective
    change D (D.symm (homologyMap g i (homologyMap f i z))) = _
    rw [AddEquiv.apply_symm_apply, cohomologyEquivModuleHomology_class]
    change homologyMap g i (homologyMap f i (closedClass i x hx)) =
      closedClass i a.1 (moduleCycle k (pdCechRings p k r) (pdCechBase p k r) i a)
    rw [homologyMap_closedClass, homologyMap_closedClass]
    congr 1
  rw [← hE]
  change homologyMap l i (homologyMap h i (E.symm (E z))) = _
  rw [AddEquiv.symm_apply_apply]
  change homologyMap l i (homologyMap h i (closedClass i x hx)) =
    closedClass i (deRhamTerm k (formVars.{u} r) i ω) _
  rw [homologyMap_closedClass, homologyMap_closedClass]
  congr 1

end SerrePositivity.BhattScholze.Prismatic
