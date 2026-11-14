module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZero
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnComparison

/-!
# pd Čech と多項式 de Rham コホモロジー

## 概要
標数 p で、総複体からの二つの射影に沿って加法同型を作る。

## 方針
第 0 行の pd Čech 同型を逆向きに、第 0 列の多項式 de Rham 同型を順向きに使う。

## 規約
基底を変えず、変数の添字だけを係数環の宇宙へ持ち上げる。

## 使われ方
結晶基底での Hodge–Tate 比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) (hp : (p : k) = 0)

/-- pd Čech コホモロジーと通常の多項式 de Rham コホモロジーとの加法同型。 -/
def pdDeRhamCechToPolynomial (i : ℕ) :
    cohomology (pdCechRings p k r) i ≃+
      (deRhamComplex k (formVars.{u} r)).homology i := by
  let := pdDeRhamColumnZeroProjection_quasiIso p k r hp
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) i
  let e := (asIso (HomologicalComplex.homologyMap (pdDeRhamColumnZeroProjection p k r) i)) ≪≫
    F.mapIso (pdDeRhamColumnZeroIso k r p hp)
  exact (pdDeRhamTotalToCech p k r i).symm.trans e.toLinearEquiv.toAddEquiv

/-- 第 0 頂点の多項式形式を任意の pd 列に入れる鎖写像。 -/
def pdDeRhamPolynomialInclusion (n : SimplexCategory) :
    deRhamComplex k (formVars.{u} r) ⟶ pdDeRhamColumn p k r n :=
  (pdDeRhamColumnZeroIso k r p hp).inv ≫
    (pdDeRhamColumnCollapseHomotopyEquiv k r n p hp).inv

/-- 第 0 頂点の包含は標数 p の pd Poincaré 擬同型。 -/
theorem pdDeRhamPolynomialInclusion_quasiIso (n : SimplexCategory) :
    QuasiIso (pdDeRhamPolynomialInclusion p k r hp n) := by
  have h : QuasiIso (pdDeRhamColumnCollapseHomotopyEquiv k r n p hp).inv := by
    constructor
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ((pdDeRhamColumnCollapseHomotopyEquiv k r n p hp).toHomologyIso i).isIso_inv
  unfold pdDeRhamPolynomialInclusion
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
