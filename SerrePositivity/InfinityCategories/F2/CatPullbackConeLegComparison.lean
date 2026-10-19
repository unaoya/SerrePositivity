module

public import SerrePositivity.InfinityCategories.F2.CatPullbackConeComparisonEdges
public import SerrePositivity.InfinityCategories.F2.CatPullbackConeLeg
public import SerrePositivity.InfinityCategories.F2.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.F2.EdgeSquareTransport

/-!
概要：読み戻した引き戻し錐の脚と置換後の射影の関手同型。
方針：各脚の自然性と coherent nerve の写像空間比較を使う。
規約：元の脚に定値 path の切断を後合成する。
使われ方：Cat_∞ の元の引き戻し錐の二射影の具体的な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：読み戻した錐の脚に切断を後合成すると置換後の通常の脚と関手同型。
方針：全錐の自然性の正方形の四頂点と各辺を coherent な指定関手へ輸送する。
規約：同じ頂点からの関手の同型を返し、頂点の自己同値は挟まない。
使われ方：元の cospan の二射影との関手同型の構成。 -/
lemma catPullbackConeFunctorLeg_section (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    Nonempty (FunctorIso
      (catPullbackConeFunctorLeg p q i ≫ (catPullbackReplacementNatTrans p q).app i)
      ((catPullbackReplacementOrdinaryCone p q).π.app i)) := by
  have h := coneHomotopy_leg_naturality (catPullbackConeHomotopy p q)
    (ULift.up (ComposableArrows.mk₀ i))
  have hs := homMk_square_transport
    (nativeConeLeg (catPullbackCone p q) (ULift.up (ComposableArrows.mk₀ i)))
    (coneHomotopyDiagramEdge (catPullbackConeHomotopy p q) (ULift.up (ComposableArrows.mk₀ i)))
    (coneHomotopyApexEdge (catPullbackConeHomotopy p q))
    (nativeConeLeg (catPullbackReplacementCone p q) (ULift.up (ComposableArrows.mk₀ i)))
    (coherentNerveEdge (catPullbackConeFunctorLeg p q i)).toTruncated
    (coherentNerveEdge ((catPullbackReplacementNatTrans p q).app i)).toTruncated
    (coherentNerveEdge (𝟙 (catPullbackObject p q))).toTruncated
    (coherentNerveEdge ((catPullbackReplacementOrdinaryCone p q).π.app i)).toTruncated
    h (catPullbackCone_vertex p q) (HomotopyLimits.strictCoherentDiagram_vertex _ i)
    (catPullbackReplacementCone_vertex p q) (HomotopyLimits.strictCoherentDiagram_vertex _ i)
    (catPullbackConeFunctorLeg_edge p q i).symm
    (catPullbackConeHomotopy_diagramEdge p q i)
    (catPullbackConeHomotopy_apexEdge p q)
    (nativeConeLeg_strict (catPullbackReplacementOrdinaryCone p q) i)
  have hid : SSet.Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (𝟙 (catPullbackObject p q))).toTruncated = 𝟙 _ := by
    rw [coherentNerveEdge_id, SSet.Edge.toTruncated_id,
      SSet.Truncated.HomotopyCategory.homMk_id]
  rw [hid, Category.id_comp] at hs
  apply catInfinity_functorIso_of_homMk_eq
  exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct (catPullbackConeFunctorLeg p q i)
      ((catPullbackReplacementNatTrans p q).app i)).toTruncated).symm.trans hs

end SerrePositivity.InfinityCategories.F2
