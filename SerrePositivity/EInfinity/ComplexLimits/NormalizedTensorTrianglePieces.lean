module
public import SerrePositivity.EInfinity.ComplexLimits.ConeTriangleIndex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementEvaluationJoin
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeSimplex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementPinchedEvaluation

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorTriangleObj {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) : Complex A :=
  if τ i = 0 then X else if τ i = 2 then Y else
    (normalizedTensorElementDiagram A X Y).obj (c.obj i)

def normalizedTensorTriangleFront {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n :=
  (normalizedTensorConeSimplex A X Y c).pullback (coneTriangleFrontIndex τ)

def normalizedTensorTriangleBack {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (normalizedTensorElementEvaluatedColumn A X Y c ⋙
    complexToClosed A)).pullback (coneTriangleBackIndex τ)

def normalizedTensorTrianglePinched {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n :=
  ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.pullback
    (coneTriangleBackIndex τ)

lemma normalizedTensorTriangleFront_obj {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 2) :
    (normalizedTensorTriangleFront A X Y c τ).obj i =
      normalizedTensorTriangleObj A X Y c τ i := by
  change normalizedTensorConeObj A X Y c (coneTriangleFrontIndex τ i) = _
  by_cases hz : τ i = 0
  · rw [coneTriangleFrontIndex_zero τ i hz, normalizedTensorConeObj_zero]
    simp only [normalizedTensorTriangleObj, hz, ↓reduceIte]
  · rw [coneTriangleFrontIndex_ne_zero τ i hz, normalizedTensorConeObj_succ]
    simp only [normalizedTensorTriangleObj, hz, hi, ↓reduceIte]

lemma normalizedTensorTriangleBack_obj {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 0) :
    (normalizedTensorTriangleBack A X Y c τ).obj i =
      normalizedTensorTriangleObj A X Y c τ i := by
  change (normalizedTensorElementEvaluatedColumn A X Y c).obj (coneTriangleBackIndex τ i) = _
  by_cases ht : τ i = 2
  · rw [coneTriangleBackIndex_two τ i ht, normalizedTensorElementEvaluatedColumn_obj_last]
    simp [normalizedTensorTriangleObj, ht]
  · rw [coneTriangleBackIndex_ne_two τ i ht,
      normalizedTensorElementEvaluatedColumn_obj_castSucc]
    simp only [normalizedTensorTriangleObj, hi, ht, ↓reduceIte]

lemma normalizedTensorTrianglePinched_obj_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i = 0) :
    (normalizedTensorTrianglePinched A X Y c τ).obj i =
      normalizedTensorTriangleObj A X Y c τ i := by
  have ht : τ i ≠ 2 := by rw [hi]; decide
  change ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.obj
    (coneTriangleBackIndex τ i) = _
  rw [coneTriangleBackIndex_ne_two τ i ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj]
  simp only [normalizedTensorTriangleObj, hi, ↓reduceIte]

lemma normalizedTensorTrianglePinched_obj_two {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i = 2) :
    (normalizedTensorTrianglePinched A X Y c τ).obj i =
      normalizedTensorTriangleObj A X Y c τ i := by
  change ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.obj
    (coneTriangleBackIndex τ i) = _
  rw [coneTriangleBackIndex_two τ i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj]
  simp [normalizedTensorTriangleObj, hi]

end SerrePositivity.EInfinity.ComplexLimits
