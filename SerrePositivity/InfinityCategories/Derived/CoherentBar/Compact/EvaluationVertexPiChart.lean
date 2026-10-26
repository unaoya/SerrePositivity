module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationPiChart
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarCompactEvaluationVertexSpace_eq (x : D)
    (y : (dgProjectiveModuleNerve R D) _⦋0⦌) :
    (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex (Simplex.vertexEquiv y))))).obj =
      (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up y))).obj :=
  congrArg (fun y => (spaceInfinityObject
    ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up y))).obj) (Simplex.vertexEquiv.symm_apply_apply y)

def dgBarCompactEvaluationVertexPiChart (x : D)
    (y : (dgProjectiveModuleNerve R D) _⦋0⦌) (n : ℕ) :
    DGBarCompactPiChart (spaceInfinityObject
      ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up y))).obj n
      (((Simplex.vertexEquiv y : ProjectiveDGModules R D).val.obj (Opposite.op x)).homology
        (-((n + 1 : ℕ) : ℤ))) :=
  (dgBarCompactEvaluationPiChart R D x (Simplex.vertexEquiv y) n).cast
    (dgBarCompactEvaluationVertexSpace_eq R D x y)

def dgBarCompactEvaluationVertexPiZeroChart (x : D)
    (y : (dgProjectiveModuleNerve R D) _⦋0⦌) :
    SSet.π₀ (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up y))).obj ≃
      ((Simplex.vertexEquiv y : ProjectiveDGModules R D).val.obj (Opposite.op x)).homology 0 :=
  dgBarCompactPiZeroChart_cast (dgBarCompactEvaluationVertexSpace_eq R D x y)
    (dgBarCompactEvaluationPiZeroChart R D x (Simplex.vertexEquiv y))

end SerrePositivity.InfinityCategories
