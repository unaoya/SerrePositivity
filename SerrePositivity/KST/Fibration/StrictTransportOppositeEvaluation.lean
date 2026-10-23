module
public import SerrePositivity.KST.Fibration.KanEnrichedOppositePointHom
public import SerrePositivity.KST.Fibration.ScaffoldWeightedResolutionPoint
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningOppositeComparison

/-! # 元の strict transport の反転比較を、同じ大域比較の二重評価に戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  (p : E ⟶ nerve I) [LeftFibration p]

/-- 元の射影そのものを共通 Hom 解像の同じ対象として表示する。 -/
def strictTransportComparisonObject : EdgewiseEnrichedObject (LeftFibrationObject (nerve I)) :=
  ⟨leftFibrationObjectOf p, trivial⟩

/-- 元の大域比較の始域値は、元の strict transport の分類候補そのもの。 -/
theorem strictTransportOppositeSource_vertex :
    (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve I)) ≫
      leftStraighteningCoherentMap I).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex (strictTransportComparisonObject p)) =
      functorVertex (leftStraighteningCandidate p) :=
  (congrArg ((leftStraighteningCoherentMap I).app (Opposite.op ⦋0⦌))
    (coherentNerveMap_vertex (edgewiseEnrichedRight (LeftFibrationObject (nerve I)))
      (strictTransportComparisonObject p))).trans (leftStraighteningCoherentMap_vertex p)

/-- 既存の対象ごとの反転比較は、同じ大域比較の同じ頂点評価と HEq。 -/
theorem strictTransportOppositeVertexIso_heq_map :
    HEq (leftStraighteningCoherentMap_oppositeVertexIso p)
      (VertexIso.map (leftStraighteningCoherentMap_oppositeIso I)
        (evaluateFunctorAt (coherentNerveVertex (strictTransportComparisonObject p)))) := by
  let e := leftStraighteningCoherentMap_oppositeIso I
  let x := coherentNerveVertex (strictTransportComparisonObject p)
  have h : HEq (leftStraighteningCoherentMap_oppositeVertexIso p) (e.app x) :=
    F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk (strictTransportOppositeSource_vertex p))
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
    functorIsoValue (leftStraighteningCoherentMap_oppositeVertexIso p) (ULift.up (nerveVertex i)) ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) i))

/-- 同じ指定成分は、同じ大域比較の同じ二重評価による像と HEq。 -/
theorem strictTransportOppositeComponentIso_heq_doubleMap (i : I) :
    HEq (strictTransportOppositeComponentIso p i)
      (VertexIso.map (leftStraighteningCoherentMap_oppositeIso I)
        (kanEnrichedDoubleEvaluation (strictTransportComparisonObject p) i)) := by
  let e := leftStraighteningCoherentMap_oppositeIso I
  let x := coherentNerveVertex (strictTransportComparisonObject p)
  let a := ULift.up.{u + 1} (nerveVertex i)
  let R := leftStraighteningCoherentMap_oppositeVertexIso p
  let F := edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve I)) ≫
    leftStraighteningCoherentMap I
  let G := leftStraighteningOppositeCoherentMap I
  have h₁ : HEq (strictTransportOppositeComponentIso p i) (functorIsoValue R a) :=
    F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk (leftStraighteningCandidate_vertex p i))
      (congrArg HomotopyCategory.mk
        (ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) i))
  have h₂ := F2.vertexIso_map_heq_of_heq R (VertexIso.map e (evaluateFunctorAt x))
    ((strictTransportOppositeSource_vertex p).symm.trans
      (evaluateFunctorAt_functorVertex x F).symm)
    ((leftStraighteningOppositeCoherentMap_vertex p).symm.trans
      (evaluateFunctorAt_functorVertex x G).symm)
    (strictTransportOppositeVertexIso_heq_map p) (evaluateFunctorAt a)
  exact h₁.trans ((functorIsoValue_heq_map R a).trans
    (h₂.trans (heq_of_eq (F2.vertexIso_map_comp e (evaluateFunctorAt x) (evaluateFunctorAt a)))))

end SerrePositivity.KST.Fibration
