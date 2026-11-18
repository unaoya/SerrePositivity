module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SemifreeRingEvaluation
public import SerrePositivity.DifferentialGraded.Module.Functor

/-!
# 元の K-projective 複体の dg nerve と同じ導来源

概要：K-projective な実複体の充満 dg 部分圏を既存の半自由分解関手へ制限する。
方針：Hom 複体・合成・同じ分解を変えずに対象条件だけを制限する。
規約：元の非有界複体と同じ宇宙を保つ。
使われ方：cofibrant probe の全高次 Hom の D(R) への接続。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

def complexKProjective : ObjectProperty (Complex A) := fun X => X.IsKProjective

abbrev KProjectiveComplex := DGFullSubcategory (Complex A) (_root_.SerrePositivity.ComplexLimits.complexKProjective A)

def kProjectiveComplexInclusion : DGFunctor A (_root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) (Complex A) :=
  dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.ComplexLimits.complexKProjective A)

def kProjectiveDerivedSource :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.ComplexLimits.kProjectiveComplexInclusion A) ≫ _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A

end SerrePositivity.ComplexLimits
