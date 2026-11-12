module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanNativeConeLeg
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.EdgeSquareTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceHomotopyClasses

/-!
概要：区間引き戻しの native 錐の脚を元の Kan 射へ読み戻す。
方針：全錐比較の自然性を指定された coherent 辺へ輸送する。
規約：頂点は元の path 引き戻し。使われ方：元の具体的な射影との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {X Y Z : KanObject.{u}}

/-- 概要：native 錐の脚の実際の Kan 射。
方針：頂点を同定して辺の逆対応。規約：全添字。使われ方：射影の回収。 -/
def intervalPullbackConeKanLeg (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    intervalPullbackKanObject f g ⟶ (kanPullbackDiagram f g).obj i :=
  kanNativeConeLeg (intervalPullbackCone f g) _
    ((intervalPullbackCone_vertex f g).trans (spaceInfinityVertex_eq_coherent _)) i

/-- 概要：読み戻しは元の脚の全一単体を保持。
方針：辺の往復。規約：厳密な式。使われ方：自然性の正方形の輸送。 -/
lemma intervalPullbackConeKanLeg_edge (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    (coherentNerveEdge (intervalPullbackConeKanLeg f g i)).edge =
      (nativeConeLeg (intervalPullbackCone f g) (ULift.up (ComposableArrows.mk₀ i))).edge :=
  kanNativeConeLeg_edge _ _ _ _

/-- 概要：元の脚に切断を合成すると置換錐の実際の射影にホモトピック。
方針：全錐の自然性と写像空間の成分判定。
規約：元の頂点の恒等射を保つ。使われ方：具体的な二射影との比較。 -/
lemma intervalPullbackConeKanLeg_section (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    Nonempty (SSet.Homotopy
      (intervalPullbackConeKanLeg f g i ≫ (intervalCospanSection f g).app i)
      ((kanPullbackCone (intervalReplacementKanEndpoint f) g).π.app i)) := by
  have h := coneHomotopy_leg_naturality (intervalPullbackConeHomotopy f g)
    (ULift.up (ComposableArrows.mk₀ i))
  have hs := homMk_square_transport
    (nativeConeLeg (intervalPullbackCone f g) (ULift.up (ComposableArrows.mk₀ i)))
    (coneHomotopyDiagramEdge (intervalPullbackConeHomotopy f g)
      (ULift.up (ComposableArrows.mk₀ i)))
    (coneHomotopyApexEdge (intervalPullbackConeHomotopy f g))
    (nativeConeLeg (intervalPullbackReplacementCone f g) (ULift.up (ComposableArrows.mk₀ i)))
    (coherentNerveEdge (intervalPullbackConeKanLeg f g i)).toTruncated
    (coherentNerveEdge ((intervalCospanSection f g).app i)).toTruncated
    (coherentNerveEdge (𝟙 (intervalPullbackKanObject f g))).toTruncated
    (coherentNerveEdge ((kanPullbackCone (intervalReplacementKanEndpoint f) g).π.app i)).toTruncated
    h ((intervalPullbackCone_vertex f g).trans (spaceInfinityVertex_eq_coherent _))
    ((kanDiagramCoherentNerve_vertex _ i).trans (spaceInfinityVertex_eq_coherent _))
    (intervalPullbackReplacementCone_vertex f g)
    (strictCoherentDiagram_vertex _ i) (intervalPullbackConeKanLeg_edge f g i).symm
    (intervalPullbackConeHomotopy_diagramEdge f g i)
    (intervalPullbackConeHomotopy_apexEdge f g)
    (nativeConeLeg_strict (kanPullbackCone (intervalReplacementKanEndpoint f) g) i)
  have hid : SSet.Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (𝟙 (intervalPullbackKanObject f g))).toTruncated = 𝟙 _ := by
    rw [coherentNerveEdge_id, SSet.Edge.toTruncated_id,
      SSet.Truncated.HomotopyCategory.homMk_id]
  rw [hid, Category.id_comp] at hs
  apply spaceInfinity_homotopy_of_homMk_eq
  exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct (intervalPullbackConeKanLeg f g i)
      ((intervalCospanSection f g).app i)).toTruncated).symm.trans hs

end SerrePositivity.InfinityCategories.F2
