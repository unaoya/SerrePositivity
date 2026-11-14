module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection
import all SerrePositivity.HomologicalAlgebra.BicomplexComponents

/-!
# 完備分冪 de Rham の係数変更と軸射影

## 概要
完備総複体の係数変更は、第 0 行と第 0 列への射影と可換である。

## 方針
二射影を総複体の成分への射影と照合し、既存の係数変更の成分公式を使う。

## 規約
係数変更を標的の係数を制限した余鎖写像として読む。

## 使われ方
BS 著者版 Theorem 6.4 の Witt 係数から剰余係数への移行。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology SerrePositivity.HomologicalAlgebra
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)

local notation "K" => pdDeRhamDoubleComplex p A r
local notation "up" => ComplexShape.up ℕ
local notation "res" => ModuleCat.restrictScalars (algebraMap A B)
local notation "R" => Functor.mapHomologicalComplex res up

private theorem rowZero_f (n : ℕ) :
    (pdDeRhamRowZeroProjection p A r).f n = componentAt K n ⟨(n,0), rfl⟩ := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  by_cases h : b = 0
  · subst b
    change a = n at hab
    subst n
    simp [pdDeRhamRowZeroProjection, totalToRowZero, rowZeroApp, componentAt, totalComponent]
  · have ha : a ≠ n := by omega
    simp [pdDeRhamRowZeroProjection, totalToRowZero, rowZeroApp, h, componentAt, totalComponent, ha]

private theorem columnZero_f (n : ℕ) :
    (pdDeRhamColumnZeroProjection p A r).f n = componentAt K n ⟨(0,n), Nat.zero_add n⟩ := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  by_cases h : a = 0
  · subst a
    have hn : b = n := (Nat.zero_add b).symm.trans hab
    cases hn
    rw [show (K).ιTotal up 0 n n _ = insertAt K n ⟨(0,n), Nat.zero_add n⟩ from rfl,
      insertAt_componentAt_eq]
    simp [pdDeRhamColumnZeroProjection, totalToColumnZero, columnZeroApp, insertAt]
  · rw [show (K).ιTotal up a b n hab = insertAt K n ⟨(a,b), hab⟩ from rfl,
      insertAt_componentAt_ne K _ _ (fun h' => h (congrArg (fun ij : totalIndex n => ij.1.1) h'))]
    simp [pdDeRhamColumnZeroProjection, totalToColumnZero, columnZeroApp, insertAt, h]

/-- 完備分冪 de Rham 総複体の半線形係数変更を余鎖写像としてまとめる。 -/
def pdDeRhamTotalCoefficientHom :
    pdDeRhamTotal p A r ⟶ Functor.obj R (pdDeRhamTotal p B r) :=
  CochainComplex.ofHom
    (fun n => ModuleCat.semilinearMapAddEquiv (algebraMap A B) _ _
      (pdTotalCoefficientMap p A B r n))
    (by
      intro n
      apply ModuleCat.hom_ext
      ext x
      exact (pdTotalCoefficientMap_d p A B r n x).symm)

/-- 第 0 行の各項の半線形係数変更。 -/
def pdRowZeroCoefficientAt (n : ℕ) :
    (((alternatingCofaceMapComplex _).obj (pdRow p A r 0)).X n) →ₛₗ[algebraMap A B]
      (((alternatingCofaceMapComplex _).obj (pdRow p B r 0)).X n) :=
  pdCoefficientAt p A B r n 0

/-- 第 0 列の各項の半線形係数変更。 -/
def pdColumnZeroCoefficientAt (n : ℕ) :
    (pdDeRhamColumn p A r ⦋0⦌).X n →ₛₗ[algebraMap A B] (pdDeRhamColumn p B r ⦋0⦌).X n :=
  pdCoefficientAt p A B r 0 n

/-- 係数変更の後に第 0 行へ射影する成分公式。 -/
theorem pdDeRhamTotalCoefficientMap_rowZero (n : ℕ) (x : (pdDeRhamTotal p A r).X n) :
    (pdDeRhamRowZeroProjection p B r).f n (pdTotalCoefficientMap p A B r n x) =
      pdRowZeroCoefficientAt p A B r n ((pdDeRhamRowZeroProjection p A r).f n x) := by
  rw [rowZero_f p A, rowZero_f p B]
  exact pdTotalCoefficientMap_component p A B r n ⟨(n,0),rfl⟩ x

/-- 係数変更の後に第 0 列へ射影する成分公式。 -/
theorem pdDeRhamTotalCoefficientMap_columnZero (n : ℕ) (x : (pdDeRhamTotal p A r).X n) :
    (pdDeRhamColumnZeroProjection p B r).f n (pdTotalCoefficientMap p A B r n x) =
      pdColumnZeroCoefficientAt p A B r n ((pdDeRhamColumnZeroProjection p A r).f n x) := by
  rw [columnZero_f p A, columnZero_f p B]
  exact pdTotalCoefficientMap_component p A B r n ⟨(0,n),Nat.zero_add n⟩ x

end SerrePositivity.BhattScholze.Prismatic
