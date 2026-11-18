module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorTriangleData
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementEvaluationIndex
public import SerrePositivity.EInfinity.Modules.SimplexClosedTransport
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleSimplex

/-!
概要：元の三相加群対象の評価と、複体側の指定三相対象を閉零同型で結ぶ。
方針：端点には恒等、中央には元の符号付き frame 同型を使う。
規約：HA 1.3.1.6、全頂点・全時刻・元の対象表示。
使われ方：M10 の全三相 cochain の評価比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ三相頂点の表示を元の閉零同型で比較する。
方針：両端は恒等、中間は同じ frame の符号付き交換。
規約：HA 1.3.1.6、全頂点。使われ方：全単体の対象表示移送。 -/
def strictRawModuleTensorTriangleEvaluationObjIso {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.ComplexLimits.complexToClosed A).obj (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x) τ i) ≅
    (_root_.SerrePositivity.ComplexLimits.complexToClosed A).obj ((moduleEvaluationDG A _ x).obj
      (strictRawModuleTensorTriangleObj A X P Q c τ i)) := by
  by_cases h0 : τ i = 0
  · simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, strictRawModuleTensorTriangleObj, h0, ↓reduceIte]
    exact Iso.refl _
  by_cases h2 : τ i = 2
  · simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, strictRawModuleTensorTriangleObj,
      h0, h2, ↓reduceIte]
    exact Iso.refl _
  · simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, strictRawModuleTensorTriangleObj,
      h0, h2, ↓reduceIte]
    exact (_root_.SerrePositivity.ComplexLimits.complexToClosed A).mapIso
      ((moduleTensorEvaluationFrameIso A _ ((strictRawModuleProbeFunctor A X).obj P) x).app
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj i)))

end SerrePositivity.EInfinity.BarrattEccles
