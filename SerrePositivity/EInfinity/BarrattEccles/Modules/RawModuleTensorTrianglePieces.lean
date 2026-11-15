module
public import SerrePositivity.EInfinity.ComplexLimits.ConeTriangleIndex
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementEvaluatedColumn
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeSimplex
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementPinchedEvaluation

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
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorTriangleObj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) : RightModule A (dgAlgebraCategory A ((assocForget A).obj X)) :=
  if τ i = 0 then ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
  else if τ i = 2 then ForgetEnrichment.to (Complex A) Q else
    ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i))

def strictRawModuleTensorTriangleFront {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n :=
  (strictRawModuleTensorConeSimplex A X P Q c).pullback (coneTriangleFrontIndex τ)

def strictRawModuleTensorTriangleBack {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (strictRawModuleTensorElementEvaluatedColumn A X P Q c)).pullback (coneTriangleBackIndex τ)

def strictRawModuleTensorTrianglePinched {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n :=
  ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c).val.pullback
    (coneTriangleBackIndex τ)

lemma strictRawModuleTensorTriangleFront_obj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 2) :
    (strictRawModuleTensorTriangleFront A X P Q c τ).obj i =
      strictRawModuleTensorTriangleObj A X P Q c τ i := by
  change strictRawModuleTensorConeObj A X P Q c (coneTriangleFrontIndex τ i) = _
  by_cases hz : τ i = 0
  · rw [coneTriangleFrontIndex_zero τ i hz, strictRawModuleTensorConeObj_zero]
    simp only [strictRawModuleTensorTriangleObj, hz, ↓reduceIte]
  · rw [coneTriangleFrontIndex_ne_zero τ i hz, strictRawModuleTensorConeObj_succ]
    simp only [strictRawModuleTensorTriangleObj, hz, hi, ↓reduceIte]

lemma strictRawModuleTensorTriangleBack_obj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 0) :
    (strictRawModuleTensorTriangleBack A X P Q c τ).obj i =
      strictRawModuleTensorTriangleObj A X P Q c τ i := by
  change ForgetEnrichment.to (Complex A)
    ((strictRawModuleTensorElementEvaluatedColumn A X P Q c).obj (coneTriangleBackIndex τ i)) = _
  by_cases ht : τ i = 2
  · rw [coneTriangleBackIndex_two τ i ht, strictRawModuleTensorElementEvaluatedColumn_obj_last]
    simp [strictRawModuleTensorTriangleObj, ht]
  · rw [coneTriangleBackIndex_ne_two τ i ht,
      strictRawModuleTensorElementEvaluatedColumn_obj_castSucc]
    simp only [strictRawModuleTensorTriangleObj, hi, ht, ↓reduceIte]

lemma strictRawModuleTensorTrianglePinched_obj_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i = 0) :
    (strictRawModuleTensorTrianglePinched A X P Q c τ).obj i =
      strictRawModuleTensorTriangleObj A X P Q c τ i := by
  have ht : τ i ≠ 2 := by rw [hi]; decide
  change ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c).val.obj
    (coneTriangleBackIndex τ i) = _
  rw [coneTriangleBackIndex_ne_two τ i ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj]
  simp only [strictRawModuleTensorTriangleObj, hi, ↓reduceIte]

lemma strictRawModuleTensorTrianglePinched_obj_two {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i = 2) :
    (strictRawModuleTensorTrianglePinched A X P Q c τ).obj i =
      strictRawModuleTensorTriangleObj A X P Q c τ i := by
  change ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c).val.obj
    (coneTriangleBackIndex τ i) = _
  rw [coneTriangleBackIndex_two τ i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj]
  simp [strictRawModuleTensorTriangleObj, hi]

end SerrePositivity.EInfinity.BarrattEccles
