module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardZeroLeg
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.FirstRowHomotopy
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardZeroLeg
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.FirstRowHomotopy
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal

/-!
# 実現の標準脚と二つの面写像を結ぶ同じホモトピー

## 概要
単体次数一の第一行の包含から、零次の二つの標準脚の間の鎖ホモトピーを作る。

## 方針
延長の行同型を用い、横微分が δ₀−δ₁ であることを第一行の零ホモトピーへ移す。

## 規約
頂点の射だけでなく、同じ全複体の直和包含をホモトピーの成分に用いる。

## 使われ方
HA 1.2.4、HTT 4.2.4.1。native 実現余錐の二次元成分への比較入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive AlgebraicTopology
open SerrePositivity.DifferentialGraded
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

/-- 横次数 -1 の行は元の単体次数一の複体。 -/
def doubleComplexFirstRowIso (X : SimplicialObject (Complex A)) :
    ((doubleComplexFunctor A).obj X).X (-1) ≅ X.obj (Opposite.op ⦋1⦌) :=
  (AlternatingFaceMapComplex.obj X).extendXIso SerrePositivity.embUp (by
    simp [SerrePositivity.embUp, ComplexShape.embeddingUpIntLE_f])

/-- 第一行から零行への横微分は、同じ二つの面写像の差。 -/
theorem firstRowDifferential (X : SimplicialObject (Complex A)) :
    (doubleComplexFirstRowIso A X).inv ≫ ((doubleComplexFunctor A).obj X).d (-1) 0 =
      (X.δ 0 - X.δ 1) ≫ (doubleComplexZeroRowIso A X).inv := by
  change _ ≫ ((AlternatingFaceMapComplex.obj X).extend SerrePositivity.embUp).d (-1) 0 = _
  rw [HomologicalComplex.extend_d_eq _ _
    (i := 1) (by simp [SerrePositivity.embUp, ComplexShape.embeddingUpIntLE_f])
    (j := 0) SerrePositivity.embUp_f_zero]
  simp [doubleComplexFirstRowIso, doubleComplexZeroRowIso,
    AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two, sub_eq_add_neg]

/-- 二つの面写像の後の標準脚は、同じ第一行の直和包含でホモトピック。 -/
def standardFaceHomotopy (X : SimplicialObject (Complex A)) :
    Homotopy (X.δ 0 ≫ standardZeroLeg A X) (X.δ 1 ≫ standardZeroLeg A X) := by
  refine Homotopy.equivSubZero.symm ?_
  have h := (firstRowHomotopy ((doubleComplexFunctor A).obj X)
    (doubleComplexZeroRow_d A X)).compLeft (doubleComplexFirstRowIso A X).inv
  have he : (doubleComplexFirstRowIso A X).inv ≫
      (((doubleComplexFunctor A).obj X).d (-1) 0 ≫
        zeroRowInclusion ((doubleComplexFunctor A).obj X) (doubleComplexZeroRow_d A X)) =
      X.δ 0 ≫ standardZeroLeg A X - X.δ 1 ≫ standardZeroLeg A X := by
    rw [← Category.assoc, firstRowDifferential]
    simp [standardZeroLeg, Category.assoc, sub_comp]
  simpa only [he, comp_zero] using h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
