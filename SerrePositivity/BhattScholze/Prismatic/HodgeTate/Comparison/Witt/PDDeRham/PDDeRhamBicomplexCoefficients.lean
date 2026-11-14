module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCoefficients
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
public import SerrePositivity.HomologicalAlgebra.BicomplexProjectionNaturality
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex

/-!
# 分冪 de Rham 双複体の係数変更

## 概要
項ごとの半線形な係数変更を、係数制限した双複体への鎖写像にまとめる。

## 方針
余面との可換性を交代和に移し、縦方向では分冪微分との可換性を使う。

## 規約
標的は係数制限して始域と同じ加群の圏で扱う。

## 使われ方
BS 著者版 Theorem 6.4 の Witt 係数の底変換と二つの比較射。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology SerrePositivity.HomologicalAlgebra
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)

local notation "up" => ComplexShape.up ℕ
local notation "res" => ModuleCat.restrictScalars (algebraMap A B)
local notation "resC" => Functor.mapHomologicalComplex res up
local notation "KB" => Functor.obj (Functor.mapHomologicalComplex resC up)
  (pdDeRhamDoubleComplex p B r)

private def rowCoefficients (j : ℕ) : pdRow p A r j ⟶ pdRow p B r j ⋙ res where
  app n := ModuleCat.semilinearMapAddEquiv (algebraMap A B) _ _
    (pdFormsCoefficientMap p A B r n j)
  naturality {m n} θ := by
    apply ModuleCat.hom_ext
    ext x
    exact pdFormsCoefficientMap_natural p A B r θ j x

private theorem rowCoefficients_comm (a j : ℕ) :
    (rowCoefficients p A B r j).app ⦋a⦌ ≫ (res).map ((pdRowComplex p B r j).d a (a + 1)) =
      (pdRowComplex p A r j).d a (a + 1) ≫ (rowCoefficients p A B r j).app ⦋a + 1⦌ := by
  have h (R : Type u) [CommRing R] :
      (pdRowComplex p R r j).d a (a + 1) =
        AlternatingCofaceMapComplex.objD (pdRow p R r j) a := by
    dsimp only [pdRowComplex, alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj]
    exact CochainComplex.of_d _ _ a
  rw [h A, h B]
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  exact ((rowCoefficients p A B r j).naturality (SimplexCategory.δ i)).symm

set_option maxHeartbeats 900000 in
-- 係数制限された複体の各項を照合する。
/-- 双複体の各項の完備係数変更。 -/
def pdDeRhamBicomplexCoefficientMap : pdDeRhamDoubleComplex p A r ⟶ KB := by
  refine HomologicalComplex₂.homMk (fun ij => (rowCoefficients p A B r ij.2).app ⦋ij.1⦌) ?_ ?_
  · intro a b j h
    obtain rfl : a + 1 = b := h
    exact rowCoefficients_comm p A B r a j
  · intro a i j h
    obtain rfl : i + 1 = j := h
    change _ ≫ (res).map ((pdDeRhamColumn p B r ⦋a⦌).d i (i + 1)) =
      (pdDeRhamColumn p A r ⦋a⦌).d i (i + 1) ≫ _
    rw [column_d_eq, column_d_eq]
    apply ModuleCat.hom_ext
    ext x
    change pdVerticalD p B r ⦋a⦌ i (pdFormsCoefficientMap p A B r ⦋a⦌ i x) =
      pdFormsCoefficientMap p A B r ⦋a⦌ (i + 1) (pdVerticalD p A r ⦋a⦌ i x)
    exact (pdFormsCoefficientMap_d p A B r ⦋a⦌ i x).symm

/-- 第 0 行への射影は、係数制限で読んだ完備係数変更と可換。 -/
theorem pdDeRhamCoefficientMap_row :
    HomologicalComplex₂.total.map (pdDeRhamBicomplexCoefficientMap p A B r) up ≫ totalToRowZero KB =
      totalToRowZero (pdDeRhamDoubleComplex p A r) ≫
        bicomplexRowMap (pdDeRhamBicomplexCoefficientMap p A B r) 0 :=
  totalToRowZero_naturality _

/-- 第 0 列への射影は、係数制限で読んだ完備係数変更と可換。 -/
theorem pdDeRhamCoefficientMap_column :
    HomologicalComplex₂.total.map (pdDeRhamBicomplexCoefficientMap p A B r) up ≫
        totalToColumnZero KB =
      totalToColumnZero (pdDeRhamDoubleComplex p A r) ≫ (pdDeRhamBicomplexCoefficientMap p A B r).f 0 :=
  totalToColumnZero_naturality _

end SerrePositivity.BhattScholze.Prismatic
