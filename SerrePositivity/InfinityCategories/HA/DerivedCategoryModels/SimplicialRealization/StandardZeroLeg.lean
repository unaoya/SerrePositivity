module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ZeroRowInclusion
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ZeroRowInclusion
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal
import all Mathlib.Algebra.Homology.TotalComplex

/-!
# 単体的実現の次数零の標準脚

## 概要
元の単体的複体の零次の項から、非正規化直和全複体への標準射を固定する。

## 方針
添字延長の零行同型の逆を、零行の標準包含と合成する。

## 規約
同じ複体の射に対する自然変換を構成し、対象ごとの脚の選択は行わない。

## 使われ方
HA 1.2.4、HTT 4.2.4.1。native 実現余錐と比較する鎖写像の零次成分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

/-- 延長された二重複体の零行は、元の単体次数零の複体そのものと同型。 -/
def doubleComplexZeroRowIso (X : SimplicialObject (Complex A)) :
    ((doubleComplexFunctor A).obj X).X 0 ≅ X.obj (Opposite.op ⦋0⦌) :=
  (AlternatingFaceMapComplex.obj X).extendXIso SerrePositivity.embUp
    SerrePositivity.embUp_f_zero

/-- 単体次数零から横方向へ出る微分は零。 -/
theorem doubleComplexZeroRow_d (X : SimplicialObject (Complex A)) (j : ℤ) :
    ((doubleComplexFunctor A).obj X).d 0 j = 0 := by
  exact (AlternatingFaceMapComplex.obj X).extend_d_from_eq_zero
    SerrePositivity.embUp 0 j 0 SerrePositivity.embUp_f_zero (by simp)

/-- 単体次数零の複体から直和全複体への、同じ零行の直和包含による標準脚。 -/
def standardZeroLeg (X : SimplicialObject (Complex A)) :
    X.obj (Opposite.op ⦋0⦌) ⟶ (directSumTotalFunctor A).obj X :=
  (doubleComplexZeroRowIso A X).inv ≫
    zeroRowInclusion ((doubleComplexFunctor A).obj X) (doubleComplexZeroRow_d A X)

/-- 標準脚は元の単体的複体の射と厳密に両立する。 -/
theorem standardZeroLeg_naturality {X Y : SimplicialObject (Complex A)} (f : X ⟶ Y) :
    standardZeroLeg A X ≫ (directSumTotalFunctor A).map f =
      f.app (Opposite.op ⦋0⦌) ≫ standardZeroLeg A Y := by
  change ((doubleComplexZeroRowIso A X).inv ≫
    zeroRowInclusion ((doubleComplexFunctor A).obj X) _) ≫
      HomologicalComplex₂.total.map ((doubleComplexFunctor A).map f) (.up ℤ) =
    f.app (Opposite.op ⦋0⦌) ≫ (doubleComplexZeroRowIso A Y).inv ≫
      zeroRowInclusion ((doubleComplexFunctor A).obj Y) _
  rw [Category.assoc, zeroRowInclusion_naturality _ _
    (doubleComplexZeroRow_d A X) (doubleComplexZeroRow_d A Y)]
  change (doubleComplexZeroRowIso A X).inv ≫
      (HomologicalComplex.extendMap (AlternatingFaceMapComplex.map f)
        SerrePositivity.embUp).f 0 ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ SerrePositivity.embUp_f_zero]
  simp [doubleComplexZeroRowIso, Category.assoc]

/-- 単体次数零の評価から実現全複体への自然変換。 -/
def standardZeroLegNatTrans :
    (evaluation SimplexCategoryᵒᵖ (Complex A)).obj (Opposite.op ⦋0⦌) ⟶
      directSumTotalFunctor A where
  app := standardZeroLeg A
  naturality _ _ f := (standardZeroLeg_naturality A f).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
