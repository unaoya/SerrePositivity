module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleValuePiChart
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeEvaluationSpace
/-!
概要：元の射影的加群の実評価値に全基点コホモロジーチャートを置く。
方針：同じ dg 評価関手の実値表示で加群の全基点チャートを輸送する。
規約：元の実頂点と評価複体を維持する。
使われ方：native bar 評価余錐の各頂点の五条件チャート。
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

lemma dgBarCompactEvaluationValueSpace_eq (x : D) (M : ProjectiveDGModules R D) :
    (spaceInfinityObject ((dgHomUnderlyingSpaceInfinity R (ProjectiveDGModules R D)).app
      (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex ((dgUniverseLiftUp R
        (RightModule R PUnit.{1})).obj ((dgBarCompactProjectiveEvaluationModuleDG R D x).obj M)))))).obj =
      (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex M)))).obj := by
  exact congrArg (fun z => (spaceInfinityObject
    ((dgHomUnderlyingSpaceInfinity R (ProjectiveDGModules R D)).app (Opposite.op ⦋0⦌)
      (ULift.up z))).obj)
    (dgFunctorNerve_vertex
      ((dgBarCompactProjectiveEvaluationModuleDG R D x).comp
        (dgUniverseLiftUp R (RightModule R PUnit.{1}))) M).symm

/-- 同じ実射影的加群の評価値の全基点チャート。 -/
def dgBarCompactEvaluationPiChart (x : D) (M : ProjectiveDGModules R D) (n : ℕ) :
    DGBarCompactPiChart
      (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex M)))).obj n
      ((M.val.obj (Opposite.op x)).homology (-((n + 1 : ℕ) : ℤ))) :=
  (dgBarCompactModuleValuePiChart R (ProjectiveDGModules R D)
    ((dgBarCompactProjectiveEvaluationModuleDG R D x).obj M) n).cast
      (dgBarCompactEvaluationValueSpace_eq R D x M)

/-- 同じ実評価値の零次数チャート。 -/
def dgBarCompactEvaluationPiZeroChart (x : D) (M : ProjectiveDGModules R D) :
    SSet.π₀ (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex M)))).obj ≃
      (M.val.obj (Opposite.op x)).homology 0 :=
  dgBarCompactPiZeroChart_cast (dgBarCompactEvaluationValueSpace_eq R D x M)
    (dgBarCompactModuleValuePiZeroChart R (ProjectiveDGModules R D)
      ((dgBarCompactProjectiveEvaluationModuleDG R D x).obj M))

end SerrePositivity.InfinityCategories
