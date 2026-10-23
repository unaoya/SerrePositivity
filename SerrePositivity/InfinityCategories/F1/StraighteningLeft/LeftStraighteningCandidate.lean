module

public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportReconstruction
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.F1.Universe.Homotopy

/-!
概要：left fibration の strict transport から得られる coherent な空間値図式。
方針：Kan 値通常関手を coherent nerve に写し、各 fiber の値を恒等射評価で比較する。
規約：これは straightening の候補であり、coherent 図式の分類や単位・余単位は別に証明する。
使われ方：Kerodon Construction 5.3.1.5、Corollary 5.6.0.6、通常の底上の構成方向。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：通常の圏の nerve 上の left fibration から 𝒮 値の coherent 図式を構成する。
方針：strict transport の Kan 値通常関手を coherent nerve の図式として表示する。
規約：底は u+1 に持ち上げる。分類の同値はこの定義に含めない。
使われ方：Kerodon Corollary 5.6.0.6、left straightening の候補となる図式。 -/
noncomputable def leftStraighteningCandidate
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u} :=
  kanDiagramCoherentNerve (leftStrictTransportFunctor p)

/-- 概要：候補図式の c での値は c の strict transport の Kan 複体を表す。
方針：Kan 値図式の coherent 表示の頂点の式を適用する。
規約：頂点は底の nerve の ULift で指定する。
使われ方：Kerodon Construction 5.3.1.5、straightening の各対象での値の確認。 -/
lemma leftStraighteningCandidate_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    (leftStraighteningCandidate p).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)) =
      spaceInfinityVertex ((leftStrictTransportFunctor p).obj c) :=
  kanDiagramCoherentNerve_vertex (leftStrictTransportFunctor p) c

/-- 概要：候補図式の unstraightening の fiber は元の left fibration の fiber の持ち上げと同値。
方針：普遍的な fiber の空間値の回収、候補の頂点の式、strict transport の恒等射評価を合成する。
規約：結論は fiber ごとの同値。全空間の底上の比較は別の証明課題。
使われ方：Kerodon Corollary 5.6.0.6、straightening 候補の fiber の整合性。 -/
noncomputable def leftStraighteningCandidateFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    QCatEquivalence
      (vertexFiber (leftUnstraighteningProjection (leftStraighteningCandidate p))
        (ULift.up (nerveVertex c)))
      ((SSet.uliftFunctor.{u + 1, u}).obj (vertexFiber p (nerveVertex c))) := by
  have he := leftUnstraighteningFiberValueEquivalence
    (leftStraighteningCandidate p) (ULift.up (nerveVertex c))
  rw [leftStraighteningCandidate_vertex] at he
  exact he.trans (leftStrictTransportEvaluate_isQCatEquivalence p c).ulift_of_kan.choose

end SerrePositivity.InfinityCategories
