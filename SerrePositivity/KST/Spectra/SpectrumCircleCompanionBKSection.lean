module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionBKPoint
public import SerrePositivity.KST.Spectra.SpectrumCircleBKParameterEdges

/-!
概要：companion の BK 切断点の中央の評価は、元の companion の円の射の指定した制限。
方針：元の円–BK 比較の中央射影と、点つき curry' の非基点側の式を使う。
規約：元の商写像と companion 経路を保持。使われ方：元の評価錐の weighted 切断との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance companionBKSectionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- companion の円の射を標準区間へ戻すと、元の companion 経路に厳密一致する。 -/
lemma circleEvaluationCompanionCircleMap_quotient (z : Sp.{u} _⦋0⦌) :
    PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫
      (circleEvaluationCompanionCircleMap z).right = circleEvaluationCompanionHomPath z :=
  PointedObject.cofiberQuotient_desc (boundary.{u} 1).ι
    (circleEvaluationPointedHom z) _ _

/-- companion の loop 点の Hom 包含への像は、元の companion の円の射の基礎 curry'。 -/
lemma circleCompanionLoopPointMap_ι (z : Sp.{u} _⦋0⦌) :
    circleCompanionLoopPointMap z ≫ PointedObject.basedHomι PointedSimplicialSet.circle
      (circleEvaluationPointedHom z) = curry' (circleEvaluationCompanionCircleMap z).right :=
  PointedMapping.unitUnderlyingHom_curry'_ι _

/-- companion の BK 点の中央射影は、指定した BK パラメーター上の同じ円の射の評価。 -/
lemma circleCompanionBKEndPointMap_central (z : Sp.{u} _⦋0⦌) :
    circleCompanionBKEndPointMap z ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram
          (nativeCotensorInput PointedSimplicialSet.circle z).val)
          (cotensor PointedSimplicialSet.circle
            (nativeCotensorInput PointedSimplicialSet.circle z).val)) (AsSmall.up.obj .one) =
      curry' (circleBKParameter.{u} ≫ (circleEvaluationCompanionCircleMap z).right) := by
  rw [circleCompanionBKEndPointMap, Category.assoc, pointLoopCircleHomComparison_central,
    ← Category.assoc]
  erw [circleCompanionLoopPointMap_ι]
  simp only [MonoidalClosed.curry']
  erw [curry_pre_app]
  rw [← Category.assoc, rightUnitor_naturality, Category.assoc]

/-- 中央 BK パラメーターの左辺の値は、元の companion 三角形の同じ Hom 経路。 -/
lemma circleCompanionBKParameter_leftEdge (z : Sp.{u} _⦋0⦌) :
    horn₂₂.ι₀₂ ≫ cospanBKWeightIso.{u}.inv.app (AsSmall.up.obj .one) ≫
      circleBKParameter ≫ (circleEvaluationCompanionCircleMap z).right =
        circleEvaluationCompanionHomPath z := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ PointedSimplicialSet.circle.right ↦
    f ≫ (circleEvaluationCompanionCircleMap z).right) circleBKParameter_leftEdge
  have he : horn₂₂.ι₀₂ ≫ cospanBKWeightIso.inv.app (AsSmall.up.obj .one) ≫
      circleBKParameter ≫ (circleEvaluationCompanionCircleMap z).right =
        PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫
          (circleEvaluationCompanionCircleMap z).right := by
    simpa only [Category.assoc] using h
  exact he.trans (circleEvaluationCompanionCircleMap_quotient z)

/-- 中央 BK パラメーターの右辺の値は、元の Hom の零頂点で定値。 -/
lemma circleCompanionBKParameter_rightEdge (z : Sp.{u} _⦋0⦌) :
    horn₂₂.ι₁₂ ≫ cospanBKWeightIso.{u}.inv.app (AsSmall.up.obj .one) ≫
      circleBKParameter ≫ (circleEvaluationCompanionCircleMap z).right =
        SSet.const (circleEvaluationPointedHom z).basepoint := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ PointedSimplicialSet.circle.right ↦
    f ≫ (circleEvaluationCompanionCircleMap z).right) circleBKParameter_rightEdge
  have he : horn₂₂.ι₁₂ ≫ cospanBKWeightIso.inv.app (AsSmall.up.obj .one) ≫
      circleBKParameter ≫ (circleEvaluationCompanionCircleMap z).right =
        SSet.const circleBasepoint ≫ (circleEvaluationCompanionCircleMap z).right := by
    simpa only [Category.assoc] using h
  rw [he, SSet.const_comp]
  exact congrArg (fun x ↦ SSet.const (X := (Δ[1] : SSet.{u})) x)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (circleEvaluationCompanionCircleMap z))

/-- companion の点を、元の固定 Hom cospan 上の全 BK 重みの切断として読む。 -/
def circleCompanionBKSection (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val) :=
  (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (circleCompanionBKEndPointMap z)

/-- companion の全切断の中央は、元の円の射の指定した BK パラメーターでの評価。 -/
lemma circleCompanionBKSection_central (z : Sp.{u} _⦋0⦌) :
    (circleCompanionBKSection z).app (AsSmall.up.obj .one) =
      circleBKParameter.{u} ≫ (circleEvaluationCompanionCircleMap z).right := by
  change (ρ_ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj
      (AsSmall.up.obj .one))).inv ≫ uncurry (circleCompanionBKEndPointMap z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
            (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
            (cotensor PointedSimplicialSet.circle
              (nativeCotensorInput PointedSimplicialSet.circle z).val))
          (AsSmall.up.obj .one)) = _
  rw [circleCompanionBKEndPointMap_central]
  simp only [MonoidalClosed.curry', uncurry_curry, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.Spectra.OmegaSpectrum
