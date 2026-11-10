module

public import SerrePositivity.HomologicalAlgebra.BicomplexProjection
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
# 総複体の二つの軸射影の自然性

## 概要
第一象限の双複体の射に関して、第 0 行と第 0 列への射影が可換である。

## 方針
総複体の各成分から前合成し、軸上と軸の外を別々に計算する。

## 使われ方
pd de Rham 双複体の多項式代入との厳密な可換性。
-/

public noncomputable section

open CategoryTheory

namespace SerrePositivity.HomologicalAlgebra

variable {C : Type*} [Category* C] [Preadditive C]

local notation "up" => ComplexShape.up ℕ

variable {K L : HomologicalComplex₂ C up up} [K.HasTotal up] [L.HasTotal up]

/-- 双複体の射の指定した行での制限。 -/
def bicomplexRowMap (f : K ⟶ L) (j : ℕ) : bicomplexRow K j ⟶ bicomplexRow L j where
  f i := (f.f i).f j
  comm' a b _ := congrArg (fun h : K.X a ⟶ L.X b => h.f j) (f.comm a b)

/-- 第 0 行への射影の自然性。 -/
theorem totalToRowZero_naturality (f : K ⟶ L) :
    HomologicalComplex₂.total.map f up ≫ totalToRowZero L =
      totalToRowZero K ≫ bicomplexRowMap f 0 := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [HomologicalComplex₂.ιTotal_map_assoc, ← Category.assoc (K.ιTotal up a b n h)]
  by_cases hb : b = 0
  · subst b
    have han : a = n := by simpa using h
    subst n
    simp [totalToRowZero, rowZeroApp, bicomplexRowMap, bicomplexRow]
  · simp [totalToRowZero, rowZeroApp, hb]

/-- 第 0 列への射影の自然性。 -/
theorem totalToColumnZero_naturality (f : K ⟶ L) :
    HomologicalComplex₂.total.map f up ≫ totalToColumnZero L =
      totalToColumnZero K ≫ f.f 0 := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [HomologicalComplex₂.ιTotal_map_assoc, ← Category.assoc (K.ιTotal up a b n h)]
  by_cases ha : a = 0
  · subst a
    have hbn : b = n := by simpa using h
    subst n
    simp [totalToColumnZero, columnZeroApp]
  · simp [totalToColumnZero, columnZeroApp, ha]

end SerrePositivity.HomologicalAlgebra
