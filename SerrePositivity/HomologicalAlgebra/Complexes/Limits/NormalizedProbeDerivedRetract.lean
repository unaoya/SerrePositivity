module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeDerivedHom

/-!
# 元の実導来 Hom 比較に使う同じ retract の型付き射

概要：元の半自由 retract の成分を同じ K-projective 導来源の端点で読む。
方針：元の成分を選び直さず、同じ Hom 比較の定義を回収する。
規約：新しい同型や射を選ばない。
使われ方：全族公式の端点照合を独立に検査し、巨大な分解定義の反復展開を避ける。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

def normalizedProbeDerivedRetractHom (Y : Complex A) :
    (HomotopyCategory.mk ((_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.semifreeKProjectiveTarget A Y))) :
        hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y)) :=
  ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionRetractIso A).app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A Y))).hom

lemma normalizedProbeDerivedHomMap_eq_postcompose (X Y : Complex A) :
    _root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedHomMap A X Y =
    _root_.SerrePositivity.ComplexLimits.normalizedKProjectiveDerivedHomMap A
      (_root_.SerrePositivity.ComplexLimits.framedLimitKProjectiveProbe A X) (_root_.SerrePositivity.ComplexLimits.semifreeKProjectiveTarget A Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose _ (_root_.SerrePositivity.ComplexLimits.normalizedProbeDerivedRetractHom A Y) := rfl

end SerrePositivity.ComplexLimits
