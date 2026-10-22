module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomFiberEvaluationEdge
public import SerrePositivity.InfinityCategories.F1.CoherentKanInvertible
public import SerrePositivity.InfinityCategories.F1.InvertibleLeftTransport

/-!
概要：分類比較の実 fiber 評価の可逆性を、同じ元の fiber 射の同値性で判定する。
方針：普遍 pointed-space 射影の transport による反映と、保存済みの辺の等式を使う。
規約：指定された元の射・辺の類を保持し、可逆性を新たな仮定にしない。
使われ方：全共変 Hom 比較の評価成分を元の pinchedHomMap へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- Kan 射の元の coherent 辺は、その同じ射が同値であるとき、かつそのときに限り可逆。 -/
lemma coherentKanEdge_invertible_iff {K L : KanObject.{u}} (f : K ⟶ L) :
    IsInvertibleEdge (coherentNerveEdge f) ↔ IsQCatEquivalence f := by
  constructor
  · intro h
    exact (pointedSpaceTransport_coherentEdge_isQCatEquivalence_iff f).mp
      (edgeTransport_isQCatEquivalence_of_isInvertibleEdge pointedSpaceProjection _ h)
  · exact coherentKanEdge_isInvertible_of_isQCatEquivalence

/-- 元の底上の辺の実 fiber 評価は、元の同じ vertexFiberMap が同値であることを検出。 -/
lemma leftFibrationFiberEvaluation_isIso_iff {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    IsIso ((hoFunctor.map (leftFibrationInfinityFiberEvaluation b)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) ↔
        IsQCatEquivalence (vertexFiberMap p q f hf b) := by
  change IsInvertibleEdge ((leftFibrationInfinityEdge p q f hf).map
    (leftFibrationInfinityFiberEvaluation b)) ↔ _
  exact (isInvertibleEdge_congr (leftFibrationFiberEvaluation_original_edge p q f hf b)).trans
    (coherentKanEdge_invertible_iff
      (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
        leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b))

end SerrePositivity.InfinityCategories.F2.Presentable
