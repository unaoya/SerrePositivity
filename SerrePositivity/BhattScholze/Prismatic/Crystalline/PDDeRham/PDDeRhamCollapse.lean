module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# pd de Rham 双複体の頂点を潰す写像

## 概要
各単体から第 0 単体への射を使って、pd 双複体を第 0 列の定数図式に写す。

## 方針
余単体構造についての de Rham 微分の自然性を、列ごとの余鎖写像に読む。

## 規約
第 0 列には頂点間の差座標がない。

## 使われ方
pd de Rham 総複体から第 0 列への比較。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology SerrePositivity.HomologicalAlgebra
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

local notation "up" => ComplexShape.up ℕ

/-- 余単体の構造射は列間の余鎖写像を誘導する。 -/
def pdDeRhamColumnMap {m n : SimplexCategory} (θ : m ⟶ n) :
    pdDeRhamColumn p k r m ⟶ pdDeRhamColumn p k r n where
  f j := (pdRow p k r j).map θ
  comm' j j' hj := by
    have h : j + 1 = j' := hj
    subst j'
    dsimp only [pdDeRhamColumn, CochainComplex.of]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact (pdDeRhamDifferential p k r j).naturality θ

private def collapseSimplex (n : SimplexCategory) : n ⟶ ⦋0⦌ :=
  SimplexCategory.const _ _ 0

private theorem collapseSimplex_unique {n : SimplexCategory} (f : n ⟶ ⦋0⦌) :
    f = collapseSimplex n := by
  ext i
  have h (a : Fin (0 + 1)) : a.val = 0 := by omega
  exact (h _).trans (h _).symm

/-- 全ての頂点を第 0 頂点に送る列間の写像。 -/
def pdDeRhamColumnCollapse (n : SimplexCategory) :
    pdDeRhamColumn p k r n ⟶ pdDeRhamColumn p k r ⦋0⦌ :=
  pdDeRhamColumnMap p k r (collapseSimplex n)

/-- 第 0 頂点の包含は列の評価の切断。 -/
theorem pdDeRhamColumnCollapse_split (n : SimplexCategory) :
    pdDeRhamColumnMap p k r (SimplexCategory.const ⦋0⦌ n 0) ≫
      pdDeRhamColumnCollapse p k r n = 𝟙 _ := by
  ext j : 1
  change (pdRow p k r j).map (SimplexCategory.const ⦋0⦌ n 0) ≫
    (pdRow p k r j).map (collapseSimplex n) = 𝟙 _
  rw [← Functor.map_comp, collapseSimplex_unique (_ ≫ _), ← collapseSimplex_unique (𝟙 ⦋0⦌)]
  exact (pdRow p k r j).map_id _

private def constColumnRow (j : ℕ) : CosimplicialObject (ModuleCat.{u} k) :=
  (Functor.const SimplexCategory).obj ((pdDeRhamColumn p k r ⦋0⦌).X j)

private def constColumnD (i j : ℕ) : constColumnRow p k r i ⟶ constColumnRow p k r j :=
  (Functor.const SimplexCategory).map ((pdDeRhamColumn p k r ⦋0⦌).d i j)

private abbrev constRowComplex (j : ℕ) :=
  (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (constColumnRow p k r j)

/-- 第 0 列を余単体の方向に定数とした双複体。 -/
def pdDeRhamConstantColumn :
    HomologicalComplex₂ (ModuleCat.{u} k) up up :=
  HomologicalComplex₂.ofGradedObject _ _
    (fun ij => (constColumnRow p k r ij.2).obj ⦋ij.1⦌)
    (fun a b j => (constRowComplex p k r j).d a b)
    (fun _ i j => (pdDeRhamColumn p k r ⦋0⦌).d i j)
    (fun a b h j => (constRowComplex p k r j).shape a b h)
    (fun _ a b h => (pdDeRhamColumn p k r ⦋0⦌).shape a b h)
    (fun a b c j => (constRowComplex p k r j).d_comp_d a b c)
    (fun _ a b c => (pdDeRhamColumn p k r ⦋0⦌).d_comp_d a b c)
    (fun a b i j => (((alternatingCofaceMapComplex (ModuleCat.{u} k)).map
      (constColumnD p k r i j)).comm a b).symm)

private def pdDeRhamRowCollapse (j : ℕ) : pdRow p k r j ⟶ constColumnRow p k r j where
  app n := (pdRow p k r j).map (collapseSimplex n)
  naturality m n θ := by
    change (pdRow p k r j).map θ ≫ (pdRow p k r j).map (collapseSimplex n) =
      (pdRow p k r j).map (collapseSimplex m) ≫ 𝟙 _
    rw [← Functor.map_comp, collapseSimplex_unique (θ ≫ _), Category.comp_id]

/-- pd 双複体から定数列双複体への座標評価。 -/
def pdDeRhamCollapse :
    pdDeRhamDoubleComplex p k r ⟶ pdDeRhamConstantColumn p k r where
  f n := pdDeRhamColumnCollapse p k r ⦋n⦌
  comm' a b _ := by
    ext j : 1
    exact ((alternatingCofaceMapComplex (ModuleCat.{u} k)).map
      (pdDeRhamRowCollapse p k r j)).comm a b

end SerrePositivity.BhattScholze.Prismatic
