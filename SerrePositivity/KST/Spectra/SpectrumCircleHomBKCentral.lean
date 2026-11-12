module

public import SerrePositivity.KST.Spectra.SpectrumCircleHomBKComparison

/-!
概要：元の cotensor–BK 比較の中央射影を、元の普遍評価と指定した円のパラメーターで計算。
方針：中央固定の係数同型、区間 end の逆の制限式、内部 Hom の前合成則を使う。
規約：全 Hom パラメーター上の厳密な式。使われ方：元の円評価錐の制限との照合。
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
local instance circleHomCentralSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 指定した BK collapse を標準の円への元の商写像に続けたパラメーター。 -/
def circleBKParameter :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj (AsSmall.up.obj .one) ⟶
      PointedSimplicialSet.circle.{u}.right :=
  cospanBKCollapse.app (AsSmall.up.obj .one) ≫
    PointedObject.cofiberQuotient (boundary.{u} 1).ι

/-- 元の Hom–BK end への比較の中央は、指定した円パラメーターへの制限そのもの。 -/
lemma pointLoopCircleHomComparison_central (X Y : OmegaSpectrum.{u}) :
    pointLoopCircleHomComparison X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) (AsSmall.up.obj .one) =
      PointedObject.basedHomι PointedSimplicialSet.circle
          (RawSpectrumMapping.pointedSpace X Y.toKanSequence) ≫
        (pre circleBKParameter.{u}).app (mappingSpace X Y) := by
  rw [pointLoopCircleHomComparison, Category.assoc, pointLoopHomBKEndIso_central,
    loopCircleBKComparison, Category.assoc, cospanBKLoopEndComparison_π,
    ← Category.assoc, loopIntervalEndCircleIso_inv_central, Category.assoc]
  change PointedObject.basedHomι PointedSimplicialSet.circle
      (RawSpectrumMapping.pointedSpace X Y.toKanSequence) ≫
    (pre (PointedObject.cofiberQuotient (boundary.{u} 1).ι)).app (mappingSpace X Y) ≫
    (pre (cospanBKCollapse.app (AsSmall.up.obj .one))).app (mappingSpace X Y) = _
  rw [← NatTrans.comp_app, ← pre_map]
  rfl

/-- cotensor の実際の比較の中央は、元の Hom 比較と同じ円パラメーターへの制限。 -/
lemma circleCotensorHomBKComparison_central (X Y : OmegaSpectrum.{u}) :
    circleCotensorHomBKComparison X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) (AsSmall.up.obj .one) =
      (cotensorMappingEquivalence X Y PointedSimplicialSet.circle).hom ≫
        PointedObject.basedHomι PointedSimplicialSet.circle
          (RawSpectrumMapping.pointedSpace X Y.toKanSequence) ≫
        (pre circleBKParameter.{u}).app (mappingSpace X Y) := by
  rw [circleCotensorHomBKComparison, Category.assoc, pointLoopCircleHomComparison_central]

/-- 中央の全パラメーターの評価は、元の cotensor 普遍評価への前合成そのもの。 -/
lemma circleCotensorHomBKComparison_uncurry (X Y : OmegaSpectrum.{u}) :
    uncurry (circleCotensorHomBKComparison X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) (AsSmall.up.obj .one)) =
      (circleBKParameter.{u} ▷ mappingSpace X (cotensor PointedSimplicialSet.circle Y)) ≫
        uncurry ((cotensorEvaluationPrecomposition X Y PointedSimplicialSet.circle).right ≫
          PointedObject.basedHomι PointedSimplicialSet.circle
            (RawSpectrumMapping.pointedSpace X Y.toKanSequence)) := by
  rw [circleCotensorHomBKComparison_central, ← Category.assoc]
  erw [uncurry_pre_app]
  rw [cotensorEvaluationPrecomposition_eq, cotensorPointedMappingComparison_right]

end SerrePositivity.KST.Spectra.OmegaSpectrum
