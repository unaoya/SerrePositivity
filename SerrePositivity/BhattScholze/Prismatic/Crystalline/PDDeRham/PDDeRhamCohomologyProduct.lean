module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCohomology
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamProjectionProduct
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRowZeroProduct
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZeroProduct
public import SerrePositivity.HomologicalAlgebra.CochainProductNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCohomology
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalLeibniz
import all SerrePositivity.CommutativeAlgebra.DeRham.CohomologyWedge

/-!
# pd de Rham のコホモロジー比較と積

## 概要
pd Čech コホモロジーと多項式 de Rham コホモロジーの比較は積を保つ。

## 方針
総複体の両射影と軸の同型は余鎖積を保つので、それぞれコホモロジーへ降ろす。

## 規約
比較は第 0 行への射影を逆向きに、第 0 列への射影を順向きに使う。

## 使われ方
結晶基底での Hodge–Tate 比較。
-/

public noncomputable section

open CategoryTheory HomologicalComplex SerrePositivity.Cosimplicial SerrePositivity.DeRham
  SerrePositivity.HomologicalAlgebra
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

local notation "T" => pdDeRhamTotal p k r
local notation "X" => pdCechRings p k r
local notation "M" => pdTotalCochainProduct p k r

private abbrev rowComparison := pdDeRhamRowZeroProjection p k r ≫ (pdDeRhamRowZeroIso p k r).hom

private theorem rowComparison_mul (i j : ℕ) (x : (T).X i) (y : (T).X j) :
    (rowComparison p k r).f (i+j) ((M).mul i j x y) =
      (moduleCochainCup k X (pdCechBase p k r)).mul i j ((rowComparison p k r).f i x)
        ((rowComparison p k r).f j y) := by
  simp only [rowComparison, comp_f, ConcreteCategory.comp_apply]
  change (pdDeRhamRowZeroIso p k r).hom.f (i+j)
    ((pdDeRhamRowZeroProjection p k r).f (i+j) (pdTotalProduct p k r i j x y)) = _

  rw [pdRowZeroProjection_mul, pdDeRhamRowZeroIso_mul]

private theorem totalToCech_apply (i : ℕ) (x : (T).homology i) :
    cohomologyEquivModuleHomology k X (pdCechBase p k r) i (pdDeRhamTotalToCech p k r i x) =
      homologyMap (rowComparison p k r) i x := by
  let := pdDeRhamRowZeroProjection_quasiIso p k r
  let e := cohomologyEquivModuleHomology k X (pdCechBase p k r) i
  let F := homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) i
  let E := asIso (homologyMap (pdDeRhamRowZeroProjection p k r) i) ≪≫
    F.mapIso (pdDeRhamRowZeroIso p k r)
  change e (e.symm (E.hom x)) = homologyMap (rowComparison p k r) i x
  let y : ((F.obj ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} k)).obj
      (toModules k X (pdCechBase p k r)))) : Type u) := E.hom x
  have h₁ : e (e.symm y) = y := e.apply_symm_apply y
  have h₂ : y = homologyMap (rowComparison p k r) i x := by
    rw [homologyMap_comp]
    rfl
  exact h₁.trans h₂

private theorem totalToCech_mul {i j : ℕ} (x : (T).homology i) (y : (T).homology j) :
    pdDeRhamTotalToCech p k r (i+j) ((M).onHomology x y) =
      cohomologyCup X (pdDeRhamTotalToCech p k r i x) (pdDeRhamTotalToCech p k r j y) := by
  apply (cohomologyEquivModuleHomology k X (pdCechBase p k r) (i+j)).injective
  rw [cohomologyEquivModuleHomology_cup, totalToCech_apply, totalToCech_apply, totalToCech_apply]
  exact CochainProduct.onHomology_natural (M) _ (rowComparison p k r) (rowComparison_mul p k r) x y

variable (hp : (p : k) = 0)

private abbrev columnComparison :=
  pdDeRhamColumnZeroProjection p k r ≫ (pdDeRhamColumnZeroIso k r p hp).hom

private theorem columnComparison_mul (i j : ℕ) (x : (T).X i) (y : (T).X j) :
    (columnComparison p k r hp).f (i+j) ((M).mul i j x y) =
      (deRhamCochainWedge k (formVars.{u} r)).mul i j ((columnComparison p k r hp).f i x)
        ((columnComparison p k r hp).f j y) := by
  simp only [columnComparison, comp_f, ConcreteCategory.comp_apply]
  change (pdDeRhamColumnZeroIso k r p hp).hom.f (i+j)
    ((pdDeRhamColumnZeroProjection p k r).f (i+j) (pdTotalProduct p k r i j x y)) = _

  rw [pdColumnZeroProjection_mul, pdDeRhamColumnZeroIso_mul]

private theorem cechToPolynomial_total (i : ℕ) (x : (T).homology i) :
    pdDeRhamCechToPolynomial p k r hp i (pdDeRhamTotalToCech p k r i x) =
      homologyMap (columnComparison p k r hp) i x := by
  let := pdDeRhamColumnZeroProjection_quasiIso p k r hp
  let e := pdDeRhamTotalToCech p k r i
  let F := homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) i
  let E := asIso (homologyMap (pdDeRhamColumnZeroProjection p k r) i) ≪≫
    F.mapIso (pdDeRhamColumnZeroIso k r p hp)
  change E.hom (e.symm (e x)) = homologyMap (columnComparison p k r hp) i x
  rw [e.symm_apply_apply, homologyMap_comp]
  rfl

/-- pd Čech と de Rham のコホモロジー同型は cup 積と外積を照合する。 -/
theorem pdDeRhamCechToPolynomial_cup {i j : ℕ} (x : cohomology X i) (y : cohomology X j) :
    pdDeRhamCechToPolynomial p k r hp (i+j) (cohomologyCup X x y) =
      deRhamCohomologyWedge k (formVars.{u} r) (pdDeRhamCechToPolynomial p k r hp i x)
        (pdDeRhamCechToPolynomial p k r hp j y) := by
  obtain ⟨a, rfl⟩ := (pdDeRhamTotalToCech p k r i).surjective x
  obtain ⟨b, rfl⟩ := (pdDeRhamTotalToCech p k r j).surjective y
  rw [← totalToCech_mul, cechToPolynomial_total, cechToPolynomial_total, cechToPolynomial_total]
  exact CochainProduct.onHomology_natural (M) _ (columnComparison p k r hp)
    (columnComparison_mul p k r hp) a b

end SerrePositivity.BhattScholze.Prismatic
