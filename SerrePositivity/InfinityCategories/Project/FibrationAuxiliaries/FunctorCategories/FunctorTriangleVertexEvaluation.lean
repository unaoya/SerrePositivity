module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBasesEvaluation

/-!
概要：同じ二変数の三角形族を頂点で評価すると、転置した同じ大域二単体の評価になる。
方針：元の二変数交換の評価と Yoneda の自然性を使う。
規約：同じ全パラメーターの三角形を保持する。
使われ方：大域可逆三角形の全頂点を同じ可逆三角形空間へ持ち上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 元の族の頂点が表す二単体は、同じ大域三角形のその頂点での評価。 -/
lemma triangleFunctorVertexSimplex_family {A Y : SSet.{u}}
    (F : A ⟶ (ihom (Δ[2] : SSet.{u})).obj Y) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.triangleFunctorVertexSimplex (F.app (Opposite.op ⦋0⦌) a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋2⦌)
        (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.internalHomFlipHomEquiv_evaluate_vertex F a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) = F.app _ a at h
  rw [← h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.triangleFunctorVertexSimplex_functorVertex, SSet.yonedaEquiv_comp]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
