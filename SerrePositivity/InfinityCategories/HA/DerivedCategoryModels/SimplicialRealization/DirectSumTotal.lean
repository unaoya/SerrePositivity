module

public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# 単体的複体の直和全複体

## 概要
単体的な非有界余鎖複体の交代面複体を、直和全複体へ送る関手を定める。

## 方針
単体次数 n を整数余鎖次数 -n に延長し、既存の直和 total 関手を合成する。

## 規約
全次数 q の成分は直和の bidegree (i,j)、i+j=q であり、i=-n に対応する。
この段では native 余極限との比較は主張しない。

## 使われ方
HTT 4.2.4.1・A.3.3、HA 1.2.4。D(A) の幾何学的実現の複体模型。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

/-- 単体的複体を、横の次数 n を -n にした二重余鎖複体へ送る。 -/
def doubleComplexFunctor :
    SimplicialObject (Complex A) ⥤ HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ) :=
  alternatingFaceMapComplex (Complex A) ⋙
    SerrePositivity.embUp.extendFunctor (Complex A)

/-- 単体的複体の非正規化された直和全複体の関手。 -/
def directSumTotalFunctor : SimplicialObject (Complex A) ⥤ Complex A :=
  doubleComplexFunctor A ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} A) (.up ℤ) (.up ℤ) (.up ℤ)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
