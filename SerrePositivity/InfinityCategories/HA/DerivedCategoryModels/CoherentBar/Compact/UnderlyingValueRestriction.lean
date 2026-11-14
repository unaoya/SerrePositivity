module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.LinearUnderlyingValueComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGCoherentClosedEdges
/-!
概要：native 基礎空間関手を同じ単位対象の Yoneda 評価として同定する。
方針：共同 Hom の curry と指定頂点評価の厳密な合成式を使う。
規約：全関手の等式を与え、頂点の値だけの比較で代用しない。
使われ方：線形 coslice 比較を実加群評価関手へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet DifferentialGraded
open scoped _root_.Simplicial

lemma dgBarCompactUnderlyingValueFunctor_eq_joint {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUnderlyingValueFunctor x =
      CartesianMonoidalCategory.lift (SSet.const (ULift.up (SSet.opObjEquiv.symm x))) (𝟙 _) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C) _

lemma dgBarCompactUnderlyingValueFunctor_unit (R : Type u) [CommRing R] (D : Type v) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUnderlyingValueFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R D) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUnderlyingValueFunctor_eq_joint _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
