module
public import SerrePositivity.EInfinity.Modules.TensorHomEvaluationValue

/-!
概要：同じ加群 frame の評価を複体の標準 frame へ全作用素に自然に比較する。
方針：符号付き交換の全自然性を全次元の実同型に束ねる。
規約：HA 1.3.1.13、元の左右のテンソル順序を保つ。
使われ方：M10 の全要素図式の対象と実評価射の係数移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：複体の標準 frame と元の加群 frame の評価は全単体で自然に同型。
方針：同じ符号付き交換を成分とする。
規約：HA 1.3.1.13、全作用素。使われ方：元の対象表示の移送。 -/
def moduleTensorEvaluationFrameIso (P : ModuleCategory A D) (x : D) :
    normalizedSimplexTensor A ((moduleEvaluation A D x).obj P) ≅
      ((moduleTensorSimplicesFunctor A D).obj P) ⋙ moduleEvaluation A D x :=
  NatIso.ofComponents (fun n => signedSwap ((moduleEvaluation A D x).obj P)
    ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n))) (by
      intro n m θ
      change _ ≫ (signedSwap _ _).hom = (signedSwap _ _).hom ≫
        (moduleEvaluation A D x).map
          (tensorModuleMap ((BarrattEccles.normalizedFunctor A).map
            (SSet.stdSimplex.map θ)) (ForgetEnrichment.to (Complex A) P))
      rw [tensorModuleMap_eval]
      exact signedSwap_naturality (𝟙 ((moduleEvaluation A D x).obj P))
        ((BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ)))

/-- 概要：全 Hom 評価の各値は同じ frame 同型で移送した元の評価射。
方針：検証済みの全転置の成分公式を使う。
規約：HA 1.3.1.13、実射。使われ方：同じ実屋根の全係数比較。 -/
lemma moduleTensorEvaluationHomMap_frame (P Q : ModuleCategory A D) (x : D)
    (n : SimplexCategory)
    (f : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ Q) :
    (moduleTensorEvaluationHomMap A D P Q x).app (op n) f =
      (moduleTensorEvaluationFrameIso A D P x).hom.app n ≫
        (moduleEvaluation A D x).map f :=
  moduleTensorEvaluationHomMap_app A D P Q x n f

end SerrePositivity.EInfinity.Modules
