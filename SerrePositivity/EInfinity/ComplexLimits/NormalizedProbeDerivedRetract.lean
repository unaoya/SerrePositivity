module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeDerivedHom

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

def normalizedProbeDerivedRetractHom (Y : Complex A) :
    (HomotopyCategory.mk ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (semifreeKProjectiveTarget A Y))) :
        hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (complexSemifreeResolutionValue A Y)) :=
  ((complexSemifreeResolutionRetractIso A).app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (complexSemifreeResolutionValue A Y))).hom

lemma normalizedProbeDerivedHomMap_eq_postcompose (X Y : Complex A) :
    normalizedProbeDerivedHomMap A X Y =
    normalizedKProjectiveDerivedHomMap A
      (framedLimitKProjectiveProbe A X) (semifreeKProjectiveTarget A Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose _ (normalizedProbeDerivedRetractHom A Y) := rfl

end SerrePositivity.EInfinity.ComplexLimits
