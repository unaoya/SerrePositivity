module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningVertices
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningFunctorIso

/-!
概要：底上の同値および coherent な図式の関手同型による straightening 候補の不変性。
方針：底上の比較を fibration の coherent nerve の頂点の同型とし、straightening の写像で送る。
規約：分類の同値性や、候補と元の一般の図式の同型はこの段階では結論しない。
使われ方：Kerodon Corollary 5.6.0.6、解像した図式上へ比較の証明を移すための整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の left fibrations の前合成同値は straightening 候補の関手同型を与える。
方針：fibration の頂点の同型を coherent な straightening 写像で送って、頂点での公式を使う。
規約：底は通常の圏 C の nerve。
使われ方：Kerodon Corollary 5.6.0.6、全空間の比較を図式全体の比較へ移す。 -/
noncomputable def leftStraighteningCandidateIsoOfPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    FunctorIso (leftStraighteningCandidate p) (leftStraighteningCandidate q) := by
  have h := VertexIso.map
    (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q f hf ef)
    (leftStraighteningCoherentMap C)
  rw [leftStraighteningCoherentMap_vertex p, leftStraighteningCoherentMap_vertex q] at h
  exact h

/-- 概要：関手同型な図式の小さい unstraightening の straightening 候補は関手同型。
方針：小さい全空間の底上の比較を straightening 候補へ送る。
規約：F と G は strict な図式に限らない。
使われ方：Kerodon Corollary 5.6.0.6、coherent な入力の同型に対する復元候補の整合性。 -/
noncomputable def smallStraighteningCandidateIsoOfFunctorIso
    {C : Type u} [Category.{u} C]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) :
    FunctorIso (leftStraighteningCandidate (smallLeftUnstraighteningProjection F))
      (leftStraighteningCandidate (smallLeftUnstraighteningProjection G)) :=
  leftStraighteningCandidateIsoOfPrecompositionEquivalence
    (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
    (smallLeftUnstraighteningComparisonOfFunctorIso η)
    (smallLeftUnstraighteningComparisonOfFunctorIso_projection η)
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence η)

/-- 概要：図式を自然な解像へ置き換えても小さい unstraightening の straightening 候補は関手同型。
方針：解像への大域的な関手同型に候補の同値不変性を適用する。
規約：候補が元の図式 F と関手同型であるという結論はまだ含めない。
使われ方：Kerodon Corollary 5.6.0.6、分類の残る比較を解像した図式で証明するための置き換え。 -/
noncomputable def smallStraighteningCandidateResolutionIso
    {C : Type u} [Category.{u} C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u}) :
    FunctorIso (leftStraighteningCandidate (smallLeftUnstraighteningProjection F))
      (leftStraighteningCandidate
        (smallLeftUnstraighteningProjection (F ≫ coherentResolutionInfinityMap))) :=
  smallStraighteningCandidateIsoOfFunctorIso (coherentResolutionDiagramComparisonIso F)

end SerrePositivity.InfinityCategories
