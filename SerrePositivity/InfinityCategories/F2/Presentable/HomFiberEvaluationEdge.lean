module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomClassificationEvaluation
public import SerrePositivity.InfinityCategories.F1.CoherentNerveHomEdgeNaturality

/-!
概要：実 fiber 評価が元の底上の比較辺を、元の fiber 射の coherent な辺へ送ること。
方針：相対 Hom の同じ零単体の計算を、豊穣作用の全 coherent 辺の自然性へ渡す。
規約：一単体の厳密な等式。射の類や値ごとの同値性だけへ弱めない。
使われ方：straightening の評価自然性を元の coslice fiber 比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 指定した元の辺の fiber 評価は、指定した同じ vertexFiberMap の辺そのもの。 -/
lemma leftFibrationFiberEvaluation_original_edge {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    (leftFibrationInfinityFiberEvaluation b).app (Opposite.op ⦋1⦌)
        (leftFibrationInfinityEdge p q f hf).edge =
      (coherentNerveEdge (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
        leftFibrationFiberObject b (leftFibrationObjectOf q) from
          vertexFiberMap p q f hf b)).edge := by
  apply coherentNerveMap_edge_of_homEquiv (leftFibrationFiberEvaluationEnriched b)
    (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from Over.homMk f hf)
  apply (SSet.unitHomEquiv _).injective
  change (relativeFunctorFiberHom p q b).app _ (relativeFunctorVertex q p f hf) =
    functorVertex (vertexFiberMap p q f hf b)
  exact relativeFunctorFiberHom_vertex p q b f hf

end SerrePositivity.InfinityCategories.F2.Presentable
