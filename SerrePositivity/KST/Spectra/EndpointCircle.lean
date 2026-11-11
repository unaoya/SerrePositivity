module

public import SerrePositivity.KST.Spectra.IntervalBoundary

/-!
概要：区間の両端を潰した商と単体的円の同型。
方針：区間の境界と二端点の余積の同型を商の普遍性へ移す。
規約：通常の点つき単体集合の同型。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop と path fiber の比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：区間の二端点を基点へ潰した円の表示。
方針：終点包含の基礎射の通常の cofiber を取る。
規約：終点包含の定義域には基点の始点も含まれる。
使われ方：Goerss–Jardine I §7。path fiber との比較に適した円。 -/
abbrev endpointCircle : PointedSimplicialSet.{u} := PointedObject.cofiber _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right

/-- 概要：二端点を潰した円から標準の単体的円への射。
方針：境界の商への射を二端点の商へ降ろす。
規約：区間からの商写像と可換。
使われ方：Goerss–Jardine I §7。二つの円の表示の比較。 -/
def endpointCircleToCircle : endpointCircle.{u} ⟶ PointedSimplicialSet.circle.{u} :=
  PointedObject.cofiberDesc _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right PointedSimplicialSet.circle.{u}
    (PointedObject.cofiberQuotient (SSet.boundary.{u} 1).ι) (by
      rw [← intervalBoundaryMap_ι, Category.assoc, PointedObject.cofiberQuotient_condition]
      simp only [comp_toUnit_assoc]
      rfl)

/-- 概要：標準の単体的円から二端点を潰した円への射。
方針：境界の端点表示の全射性で商の条件を検査する。
規約：区間からの商写像と可換。
使われ方：Goerss–Jardine I §7。二つの円の表示の比較。 -/
def circleToEndpointCircle : PointedSimplicialSet.circle.{u} ⟶ endpointCircle.{u} :=
  PointedObject.cofiberDesc (SSet.boundary.{u} 1).ι endpointCircle.{u}
    (PointedObject.cofiberQuotient _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right) (by
      apply (cancel_epi intervalBoundaryMap.{u}).mp
      rw [← Category.assoc, intervalBoundaryMap_ι, PointedObject.cofiberQuotient_condition]
      simp only [comp_toUnit_assoc])

/-- 概要：二端点を潰した商は単体的円と同型。
方針：商からの射を区間へ引き戻して両方向の合成を検査する。
規約：通常の点つき同型であり、弱同値の仮定を使わない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の表示の比較。 -/
def endpointCircleIso : endpointCircle.{u} ≅ PointedSimplicialSet.circle.{u} where
  hom := endpointCircleToCircle
  inv := circleToEndpointCircle
  hom_inv_id := by
    apply PointedObject.cofiber_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right
    simp [endpointCircleToCircle, circleToEndpointCircle, Under.comp_right]
  inv_hom_id := by
    apply PointedObject.cofiber_hom_ext (SSet.boundary.{u} 1).ι
    simp [endpointCircleToCircle, circleToEndpointCircle, Under.comp_right]
    rfl

end

end SerrePositivity.KST.Spectra
