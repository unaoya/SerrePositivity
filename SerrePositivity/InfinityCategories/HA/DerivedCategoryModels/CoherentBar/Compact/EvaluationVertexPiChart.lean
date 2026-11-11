module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationPiChart
/-!
概要：評価チャートを任意の native 頂点の元の表示で与える。
方針：実 dg 頂点の全単射の逆則によって同じ頂点へ戻す。
規約：coherent 図式の実頂点を canonical 頂点へ置換したままにしない。
使われ方：元の native bar 余錐の段階と頂点の五条件チャート。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarCompactEvaluationVertexSpace_eq (x : D)
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv y))))).obj =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up y))).obj :=
  congrArg (fun y => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up y))).obj) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm_apply_apply y)

def dgBarCompactEvaluationVertexPiChart (x : D)
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up y))).obj n
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D).val.obj (Opposite.op x)).homology
        (-((n + 1 : ℕ) : ℤ))) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiChart R D x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv y) n).cast
    (dgBarCompactEvaluationVertexSpace_eq R D x y)

def dgBarCompactEvaluationVertexPiZeroChart (x : D)
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D) _⦋0⦌) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up y))).obj ≃
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D).val.obj (Opposite.op x)).homology 0 :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiZeroChart_cast (dgBarCompactEvaluationVertexSpace_eq R D x y)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationPiZeroChart R D x (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv y))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
