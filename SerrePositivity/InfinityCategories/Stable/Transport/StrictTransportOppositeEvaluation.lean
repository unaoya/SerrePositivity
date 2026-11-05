module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Coherent.Quasicategory
public import SerrePositivity.InfinityCategories.Core.CatInfinity.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.NervePostcomposition
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftCoherentTransportReconstruction
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagram
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramEdgewise
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramOppositeComparison
public import SerrePositivity.InfinityCategories.F1.KanModels.KanOppositeCoefficients
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningCandidate
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningOppositeComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningVertices
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransport
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportDomains
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportJointEvaluation
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedCategory
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEnrichedComparison
public import SerrePositivity.InfinityCategories.F1B.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldWeightedResolutionPoint
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValue
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValueCurry
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDoubleEvaluation

/-! # 元の strict transport の反転比較を、同じ大域比較の二重評価に戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Stable.Transport
open SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  (p : E ⟶ nerve I) [LeftFibration p]

/-- 元の射影そのものを共通 Hom 解像の同じ対象として表示する。 -/
def strictTransportComparisonObject : EdgewiseEnrichedObject (LeftFibrationObject (nerve I)) :=
  ⟨leftFibrationObjectOf p, trivial⟩

/-- 元の大域比較の始域値は、元の strict transport の分類候補そのもの。 -/
theorem strictTransportOppositeSource_vertex :
    (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve I)) ≫
      leftStraighteningCoherentMap I).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p)) =
      functorVertex (leftStraighteningCandidate p) :=
  (congrArg ((leftStraighteningCoherentMap I).app (Opposite.op ⦋0⦌))
    (coherentNerveMap_vertex (edgewiseEnrichedRight (LeftFibrationObject (nerve I)))
      (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p))).trans (leftStraighteningCoherentMap_vertex p)

/-- 既存の対象ごとの反転比較は、同じ大域比較の同じ頂点評価と HEq。 -/
theorem strictTransportOppositeVertexIso_heq_map :
    HEq (leftStraighteningCoherentMap_oppositeVertexIso p)
      (VertexIso.map (leftStraighteningCoherentMap_oppositeIso I)
        (evaluateFunctorAt (coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p)))) := by
  let e := leftStraighteningCoherentMap_oppositeIso I
  let x := coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p)
  have h : HEq (leftStraighteningCoherentMap_oppositeVertexIso p) (e.app x) :=
    F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeSource_vertex p))
      (congrArg HomotopyCategory.mk (leftStraighteningOppositeCoherentMap_vertex p))
  exact h.trans (F2.functorIso_app_heq_evaluate e x)

/-- 元の大域比較は、元の豊穣図式の反転実現同型の端点表示だけを変えたもの。 -/
theorem strictTransportOppositeIso_heq :
    HEq (leftStraighteningCoherentMap_oppositeIso I)
      (relativeSectionEnrichedDiagram (strictTransportDomains I)).oppositeRealizationIso := by
  unfold leftStraighteningCoherentMap_oppositeIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact hcast _ _

/-- 元の strict transport 反転比較の指定成分を、同じ二つの Kan 値へ表示する。 -/
def strictTransportOppositeComponentIso (i : I) :
    VertexIso (spaceInfinityVertex ((leftStrictTransportFunctor p).obj i))
      (spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj i))) :=
  (eqToIso (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p i))).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue (leftStraighteningCoherentMap_oppositeVertexIso p) (ULift.up (nerveVertex i)) ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) i))

/-- 同じ指定成分は、同じ大域比較の同じ二重評価による像と HEq。 -/
theorem strictTransportOppositeComponentIso_heq_doubleMap (i : I) :
    HEq (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso p i)
      (VertexIso.map (leftStraighteningCoherentMap_oppositeIso I)
        (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p) i)) := by
  let e := leftStraighteningCoherentMap_oppositeIso I
  let x := coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject p)
  let a := ULift.up.{u + 1} (nerveVertex i)
  let R := leftStraighteningCoherentMap_oppositeVertexIso p
  let F := edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve I)) ≫
    leftStraighteningCoherentMap I
  let G := leftStraighteningOppositeCoherentMap I
  have h₁ : HEq (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso p i) (_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue R a) :=
    F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p i))
      (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) i))
  have h₂ := F2.vertexIso_map_heq_of_heq R (VertexIso.map e (evaluateFunctorAt x))
    ((_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeSource_vertex p).symm.trans
      (evaluateFunctorAt_functorVertex x F).symm)
    ((leftStraighteningOppositeCoherentMap_vertex p).symm.trans
      (evaluateFunctorAt_functorVertex x G).symm)
    (_root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeVertexIso_heq_map p) (evaluateFunctorAt a)
  exact h₁.trans ((_root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_heq_map R a).trans
    (h₂.trans (heq_of_eq (F2.vertexIso_map_comp e (evaluateFunctorAt x) (evaluateFunctorAt a)))))

end SerrePositivity.InfinityCategories.Stable.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportComparisonObject := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportComparisonObject

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportOppositeComponentIso := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportOppositeComponentIso_heq_doubleMap := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso_heq_doubleMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportOppositeIso_heq := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeIso_heq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportOppositeSource_vertex := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeSource_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportOppositeVertexIso_heq_map := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeVertexIso_heq_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportOppositeComponentIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictTransportOppositeComponentIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Transport.strictTransportOppositeComponentIso._proof_2
