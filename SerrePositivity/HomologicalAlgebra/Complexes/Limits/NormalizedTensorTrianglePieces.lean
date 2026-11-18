module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleIndex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementEvaluationJoin
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeSimplex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementPinchedEvaluation

/-!
概要：元の cone・評価余錐・pinched 単体を三相時刻で引き戻し、同じ対象族へ比較する。
方針：元の引き戻し単体・実射・端点の等式輸送を保持する。
規約：全 HA 方程式は別工程。使われ方：大域評価三角形の実混合単体。
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
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorTriangleObj {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) : Complex A :=
  if τ i = 0 then X else if τ i = 2 then Y else
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i)

def normalizedTensorTriangleFront {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n :=
  (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c).pullback (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ)

def normalizedTensorTriangleBack {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c ⋙
    _root_.SerrePositivity.ComplexLimits.complexToClosed A)).pullback (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ)

def normalizedTensorTrianglePinched {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n :=
  ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.pullback
    (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ)

lemma normalizedTensorTriangleFront_obj {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 2) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ).obj i =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj A X Y c τ i := by
  change _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj A X Y c (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ i) = _
  by_cases hz : τ i = 0
  · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ i hz, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_zero]
    simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, hz, ↓reduceIte]
  · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ i hz, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeObj_succ]
    simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, hz, hi, ↓reduceIte]

lemma normalizedTensorTriangleBack_obj {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 0) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ).obj i =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj A X Y c τ i := by
  change (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn A X Y c).obj (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ i) = _
  by_cases ht : τ i = 2
  · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ i ht, _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_obj_last]
    simp [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, ht]
  · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ i ht,
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluatedColumn_obj_castSucc]
    simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, hi, ht, ↓reduceIte]

lemma normalizedTensorTrianglePinched_obj_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i = 0) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).obj i =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj A X Y c τ i := by
  have ht : τ i ≠ 2 := by rw [hi]; decide
  change ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.obj
    (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ i) = _
  rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ i ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj]
  simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, hi, ↓reduceIte]

lemma normalizedTensorTrianglePinched_obj_two {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i = 2) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).obj i =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj A X Y c τ i := by
  change ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.obj
    (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ i) = _
  rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj]
  simp [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, hi]

end SerrePositivity.ComplexLimits
