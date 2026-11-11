module

public import SerrePositivity.KST.Spectra.MappingFiberPaths
public import SerrePositivity.KST.Spectra.PointedMappingFamilyVertices

/-!
概要：loop を path として読む射を、区間から円への標準商で計算する。
方針：円の二つの表示の商への射と、内部 Hom の前合成の合成法則を使う。
規約：区間の向きを反転させない。
使われ方：Goerss–Jardine I §7–8。円の代表と path の終点の辺の照合。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 二端点を潰す区間から標準の円への点つき射。 -/
def circleIntervalProjection : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} ⟶ PointedSimplicialSet.circle.{u} :=
  pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u} ≫ endpointCircleIso.{u}.hom

/-- 円への区間の商は標準の境界の商の射と厳密に一致する。 -/
lemma circleIntervalProjection_right : circleIntervalProjection.{u}.right =
    PointedObject.cofiberQuotient (boundary.{u} 1).ι := by
  change PointedObject.cofiberQuotient _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right ≫
    endpointCircleToCircle.{u}.right = _
  dsimp only [endpointCircleToCircle]
  exact PointedObject.cofiberQuotient_desc _ _ _ _

/-- loop の path 表示は区間からの標準商による前合成。 -/
lemma loopToPath_eq_pre (Y : PointedSimplicialSet.{u}) :
    PointedMapping.loopToPath Y = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed circleIntervalProjection.{u} Y := by
  dsimp only [PointedMapping.loopToPath]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  change (MonoidalClosed.pre endpointCircleIso.{u}.hom).app Y ≫
    (MonoidalClosed.pre (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u})).app Y =
      (MonoidalClosed.pre circleIntervalProjection.{u}).app Y
  rw [circleIntervalProjection, MonoidalClosed.pre_map, NatTrans.comp_app]

/-- loop の頂点を path として読むと、円からの射を区間へ引き戻した頂点になる。 -/
lemma loopToPath_familyVertex (Y : PointedSimplicialSet.{u})
    (f : PointedSimplicialSet.circle.{u} ⟶ Y) :
    (PointedMapping.loopToPath Y).right.app _ (PointedMapping.familyVertex f) =
      PointedMapping.familyVertex (circleIntervalProjection ≫ f) := by
  rw [loopToPath_eq_pre, PointedMapping.familyVertex_pre]

end
end SerrePositivity.KST.Spectra
