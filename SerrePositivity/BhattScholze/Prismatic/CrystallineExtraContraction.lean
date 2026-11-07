module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology
public import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# 切断付き余分な座標の収縮

## 概要
任意の余単体的可換代数に切断付き Čech 余脈体をテンソルしてもコホモロジーは変わらない。

## 方針
余脈体の余増大のホモトピーを項ごとの余積に移す。

## 規約
可換代数の余積は係数環上で取る。

## 使われ方
結晶模型で余分な δ 座標の因子を分離した後の比較。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {C : Type u} [Category C] [HasBinaryCoproducts C]

/-- 可換代数のテンソル積に用いる、項ごとの余積関手。 -/
def crystallineAlgebraCoprod : C × C ⥤ C where
  obj X := X.1 ⨿ X.2
  map f := coprod.map f.1 f.2
  map_id _ := coprod.map_id_id
  map_comp _ _ := (coprod.map_map _ _ _ _).symm

variable (f : Arrow C)
variable [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)]

/-- 項ごとの余積に Čech 余増大を加える。 -/
@[expose] def crystallineAddSplitCech (N : CosimplicialObject C) :
    N.prod' ((Functor.const SimplexCategory).obj f.left) ⋙ crystallineAlgebraCoprod ⟶
      N.prod' f.cechConerve ⋙ crystallineAlgebraCoprod :=
  Functor.whiskerRight (NatTrans.prod' (𝟙 N) f.augmentedCechConerve.hom) crystallineAlgebraCoprod

/-- 切断付き Čech 余脈体の因子を加える写像は余鎖ホモトピー同値。 -/
def crystallineAddSplitCech_equiv (s : f.right ⟶ f.left) (hs : f.hom ≫ s = 𝟙 f.left)
    (N : CosimplicialObject C) (F : C ⥤ AddCommGrpCat.{u}) :
    HomotopyEquiv
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
        (N.prod' ((Functor.const SimplexCategory).obj f.left) ⋙ crystallineAlgebraCoprod ⋙ F))
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
        (N.prod' f.cechConerve ⋙ crystallineAlgebraCoprod ⋙ F)) :=
  cechSplitCochainEquiv f s hs N (crystallineAlgebraCoprod ⋙ F)

end SerrePositivity.BhattScholze.Prismatic
