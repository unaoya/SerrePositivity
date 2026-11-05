module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.LinearUnderlyingValueComparison
public import SerrePositivity.InfinityCategories.Derived.DGCoherentClosedEdges
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DoldKanComparison
open scoped _root_.Simplicial

lemma dgBarCompactUnderlyingValueFunctor_eq_joint {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    dgBarCompactUnderlyingValueFunctor x =
      CartesianMonoidalCategory.lift (SSet.const (ULift.up (SSet.opObjEquiv.symm x))) (𝟙 _) ≫
        homInfinityJointEvaluation C := by
  exact curry_evaluateFunctorAt_vertex (homInfinityJointEvaluation C) _

lemma dgBarCompactUnderlyingValueFunctor_unit (R : Type u) [CommRing R] (D : Type v) :
    dgBarCompactUnderlyingValueFunctor (dgHomModuleUnitVertex R D) =
      dgHomUnderlyingSpaceInfinity R D :=
  dgBarCompactUnderlyingValueFunctor_eq_joint _

end SerrePositivity.InfinityCategories
