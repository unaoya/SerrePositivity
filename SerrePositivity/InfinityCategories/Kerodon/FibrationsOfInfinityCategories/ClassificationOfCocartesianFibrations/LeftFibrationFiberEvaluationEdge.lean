module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFiberEvaluation

/-!
概要：同じ底上の射のfiber評価のcoherentな像は、元の実際のfiber射。
方針：元の豊穣Homの零次元の作用とcoherentな辺の自然性を適用する。
規約：全空間・射・底の等式を保持し、弱同値を仮定しない。
使われ方：元の全straightening比較の指定単位の評価。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元のfiber評価が元の底上の射のcoherentな辺へ与える像は、同じvertexFiberMapのcoherentな辺そのもの。 -/
lemma leftFibrationInfinityFiberEvaluation_edge {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    (leftFibrationInfinityFiberEvaluation b).app (Opposite.op ⦋1⦌)
        (leftFibrationInfinityEdge p q f hf).edge =
      (coherentNerveEdge (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
          leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)).edge := by
  apply coherentNerveMap_edge_of_homEquiv (leftFibrationFiberEvaluationEnriched b)
    (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from
      Over.homMk (U := Over.mk p) (V := Over.mk q) f hf)
  apply (SSet.unitHomEquiv _).injective
  change (relativeFunctorFiberHom p q b).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex q p f hf) = functorVertex (vertexFiberMap p q f hf b)
  exact relativeFunctorFiberHom_vertex p q b f hf
/-- 元のfiber評価の射の像は、同じvertexFiberMapのcoherentな辺の類とArrowとして一致する。 -/
lemma leftFibrationInfinityFiberEvaluation_hom_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk ((hoFunctor.map (leftFibrationInfinityFiberEvaluation b)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) =
      Arrow.mk (HomotopyCategory.homMk (coherentNerveEdge
        (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
          leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b))) := by
  change Arrow.mk (HomotopyCategory.homMk
    ((leftFibrationInfinityEdge p q f hf).map (leftFibrationInfinityFiberEvaluation b))) = _
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact leftFibrationInfinityFiberEvaluation_edge p q f hf b

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end
