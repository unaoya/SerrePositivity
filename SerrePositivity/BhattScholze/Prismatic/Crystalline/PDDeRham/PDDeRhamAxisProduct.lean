module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBigradedLeibniz
public import SerrePositivity.HomologicalAlgebra.CochainProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.AWBilinear

/-!
# pd de Rham の第 0 行と各列の余鎖積

## 概要
第 0 行の Alexander–Whitney 外積と各列の外積を余鎖積として読む。

## 方針
余面方向と de Rham 方向でそれぞれの Leibniz 則を使う。

## 規約
第 0 行と第 0 列では総複体の積の交差符号は消える。

## 使われ方
総複体から二つの射影の乗法性。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology SerrePositivity.Cosimplicial
  SerrePositivity.HomologicalAlgebra
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

local notation "Y" => pdRow p k r 0
private abbrev rowZeroComplex := (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj Y
local notation "R" => rowZeroComplex p k r

set_option backward.isDefEq.respectTransparency false in
/-- 第 0 行の積は余単体方向の Alexander–Whitney 外積。 -/
def pdRowZeroCochainProduct :
    CochainProduct ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (pdRow p k r 0)) where
  mul i j := (pdWedge p k r ⦋i+j⦌ 0 0).compl₁₂
    ((Y).map (frontFace i j)).hom ((Y).map (backFace i j)).hom
  leibniz i j x y := by
    let H := moduleCofaceDifferential_awBilinear Y Y Y (fun n => pdWedge p k r n 0 0)
      (fun θ f g => pdWedge_natural p k r θ 0 0 f g) x y
    have h (n : ℕ) : (R).d n (n+1) = moduleCofaceDifferential Y n := by
      change (AlternatingCofaceMapComplex.obj (pdRow p k r 0)).d n (n+1) = _
      dsimp only [AlternatingCofaceMapComplex.obj, CochainComplex.of]
      rw [CochainComplex.of_d]
      rfl
    rw [h, h, h]
    exact H

set_option backward.isDefEq.respectTransparency false in
/-- 列の完備 pd de Rham 外積は微分と Leibniz 則で両立する。 -/
def pdColumnCochainProduct (n : ℕ) : CochainProduct (pdDeRhamColumn p k r ⦋n⦌) where
  mul := pdWedge p k r ⦋n⦌
  leibniz i j x y := by
    have h (a : ℕ) : (pdDeRhamColumn p k r ⦋n⦌).d a (a+1) = pdVerticalD p k r ⦋n⦌ a :=
      column_d_eq p k r n a
    rw [h, h, h]
    exact pdVerticalD_wedge p k r ⦋n⦌ x y

end SerrePositivity.BhattScholze.Prismatic
