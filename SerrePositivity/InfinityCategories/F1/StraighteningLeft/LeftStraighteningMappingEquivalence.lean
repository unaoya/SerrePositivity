module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRelativeEquivalence
public import SerrePositivity.InfinityCategories.F1.Universe.RelativeFunctor

/-!
概要：元の小さい相対写像空間を、直値の straightening 候補の復元間の相対写像空間と比較する。
方針：相対関手空間の宇宙移送の同型と、二つの底上の復元比較による同値を合成する。
規約：これは fibration 間の相対写像空間の比較。coherent な図式の変換の写像空間との比較は別に構成する。
使われ方：Kerodon Corollary 5.6.0.6、straightening の写像空間の比較の fibration 側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：元の小さい二つの left fibrations の相対写像空間の持ち上げは、その候補の復元間の相対写像空間と同値。
方針：宇宙移送の厳密な同型の後に、復元比較による始域・標的の置き換えを適用する。
規約：図式の値は反転せず、底の nerve と写像空間の宇宙を u+1 に揃える。
使われ方：Kerodon Corollary 5.6.0.6、小さい fibration の相対写像空間から復元への比較。 -/
noncomputable def leftStraighteningCandidateMappingEquivalence
    {C : Type u} [Category.{u} C] {E F : SSet.{u}}
    (p : E ⟶ nerve C) (q : F ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace q p))
      (relativeFunctorSpace (leftUnstraighteningProjection (leftStraighteningCandidate q))
        (leftUnstraighteningProjection (leftStraighteningCandidate p))) :=
  (qCatEquivalenceOfIso (uliftRelativeFunctorIso.{u, u + 1} q p)).trans
    (leftStraighteningCandidateRelativeEquivalence p q)

end SerrePositivity.InfinityCategories
