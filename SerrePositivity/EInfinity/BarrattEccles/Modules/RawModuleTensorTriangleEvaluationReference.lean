module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorTriangleEvaluationObjects

/-!
概要：複体側の指定実三相単体を、元の加群三相対象の評価表示へ移す。
方針：同じ全対象同型により既存の全単体を係数移送する。
規約：HA 1.3.1.6、全 HA 方程式。加群データの評価との一致は別に証明する。
使われ方：M10 の同じ三相データの全評価比較。
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

/-- 概要：評価した元の三相対象上に、同じ複体側の実三相単体を表示する。
方針：端点の恒等と中央の元の符号付き frame 同型で全 cochain を移送する。
規約：HA 1.3.1.6、全有限部分集合。使われ方：全 HA 方程式の評価による反映。 -/
def strictRawModuleTensorTriangleEvaluationReference {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
      A (Complex A) n :=
  simplexClosedTransport A (Complex A)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x) τ)
    (fun i => (moduleEvaluationDG A _ x).obj (strictRawModuleTensorTriangleObj A X P Q c τ i))
    (strictRawModuleTensorTriangleEvaluationObjIso A X P Q c τ x)

end SerrePositivity.EInfinity.BarrattEccles
