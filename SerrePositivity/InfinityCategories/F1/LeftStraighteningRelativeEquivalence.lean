module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorComparisonEquivalence
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningReconstruction

/-!
概要：二つの left fibrations の相対写像空間を直値の straightening 候補の復元どうしの写像空間と比較する。
方針：元の全空間からの底上の復元比較を、始域と標的の双方に適用する。
規約：元の全空間と底を u+1 へ持ち上げる。図式の値を反転しない。
使われ方：Kerodon Corollary 5.6.0.6、straightening の復元の相対写像空間での比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：二つの left fibrations の持ち上げた相対写像空間と、straightening 候補の復元どうしの相対写像空間は同値。
方針：二つの復元比較に、相対関手空間の始域・標的の同時置き換えを適用する。
規約：分類の関手空間の同値そのものとは区別し、復元された fibration 間の写像空間を比較する。
使われ方：Kerodon Corollary 5.6.0.6、直値の straightening の写像空間の比較の fibration 側。 -/
noncomputable def leftStraighteningCandidateRelativeEquivalence
    {C : Type u} [Category.{u} C] {E F : SSet.{u}}
    (p : E ⟶ nerve C) (q : F ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence
      (relativeFunctorSpace ((SSet.uliftFunctor.{u + 1, u}).map q)
        ((SSet.uliftFunctor.{u + 1, u}).map p))
      (relativeFunctorSpace (leftUnstraighteningProjection (leftStraighteningCandidate q))
        (leftUnstraighteningProjection (leftStraighteningCandidate p))) := by
  letI : LeftFibration (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map q)).hom :=
    HomotopyLimits.leftFibration_uliftFunctor_map q
  letI : LeftFibration (Over.mk (leftUnstraighteningProjection (leftStraighteningCandidate q))).hom :=
    inferInstanceAs (LeftFibration (leftUnstraighteningProjection (leftStraighteningCandidate q)))
  exact relativeFunctorEquivalenceOfComparisons
    (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map p))
    (Over.mk (leftUnstraighteningProjection (leftStraighteningCandidate p)))
    (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map q))
    (Over.mk (leftUnstraighteningProjection (leftStraighteningCandidate q)))
    (Over.homMk (leftStraighteningCandidateComparison p)
      (leftStraighteningCandidateComparison_projection p))
    (Over.homMk (leftStraighteningCandidateComparison q)
      (leftStraighteningCandidateComparison_projection q))
    (leftStraighteningCandidateComparison_isPrecompositionEquivalence p)
    (leftStraighteningCandidateComparison_isPrecompositionEquivalence q)

end SerrePositivity.InfinityCategories
