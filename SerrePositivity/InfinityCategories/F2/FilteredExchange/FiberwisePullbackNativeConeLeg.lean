module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackNativeConeEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanIntervalConeLeg

/-!
概要：引き戻し全空間の native な脚を元の Kan 比較と区間引き戻しの脚へ照合する。
方針：全錐の自然性を実際の三対象間の射へ読み戻す。
規約：比較射も頂点も元のもの。使われ方：coherent filtered 引き戻しの射影の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {E D H B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
  [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]

/-- 概要：全空間の native な脚の実際の Kan 射。
方針：指定頂点で辺を読み戻す。規約：元の一単体。使われ方：元の射影との比較。 -/
def fiberwisePullbackNativeConeKanLeg (i : AsSmall.{u} WalkingCospan) :
    fiberwisePullbackTotalKanObject p f g ⟶
      (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).obj i :=
  kanNativeConeLeg (fiberwisePullbackNativeCone p f g) _
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _)) i

/-- 概要：元の全空間の脚は、元の比較射と区間錐の脚の合成にホモトピック。
方針：全錐自然性の四辺を指定 coherent 辺へ輸送する。
規約：頂点の自己同値を追加しない。使われ方：具体的な射影との照合。 -/
lemma fiberwisePullbackNativeConeKanLeg_comparison (i : AsSmall.{u} WalkingCospan) :
    Nonempty (SSet.Homotopy (fiberwisePullbackNativeConeKanLeg p f g i)
      (fiberwisePullbackComparisonKanMap p f g ≫
        intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g) i)) := by
  let j := ULift.up.{u + 1} (ComposableArrows.mk₀ i)
  let K := (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)).obj i
  have hv := (kanDiagramCoherentNerve_vertex
    (kanPullbackDiagram (continuousKanMap f) (continuousKanMap g)) i).trans
      (spaceInfinityVertex_eq_coherent _)
  have hr : (coneHomotopyDiagramEdge (fiberwisePullbackNativeConeHomotopy p f g) j).edge =
      (coherentNerveEdge (𝟙 K)).edge := by
    rw [fiberwisePullbackNativeConeHomotopy_diagramEdge]
    calc
      _ = PinchedHom.constant (coherentNerveVertex K) 1 :=
        congrArg (fun v => PinchedHom.constant v 1) hv
      _ = _ := by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl
  have hs := homMk_square_transport
    (nativeConeLeg (fiberwisePullbackNativeCone p f g) j)
    (coneHomotopyDiagramEdge (fiberwisePullbackNativeConeHomotopy p f g) j)
    (coneHomotopyApexEdge (fiberwisePullbackNativeConeHomotopy p f g))
    (nativeConeLeg (intervalPullbackCone (continuousKanMap f) (continuousKanMap g)) j)
    (coherentNerveEdge (fiberwisePullbackNativeConeKanLeg p f g i)).toTruncated
    (coherentNerveEdge (𝟙 K)).toTruncated
    (coherentNerveEdge (fiberwisePullbackComparisonKanMap p f g)).toTruncated
    (coherentNerveEdge
      (intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g) i)).toTruncated
    (coneHomotopy_leg_naturality (fiberwisePullbackNativeConeHomotopy p f g) j)
    ((fiberwisePullbackNativeCone_vertex p f g).trans (spaceInfinityVertex_eq_coherent _)) hv
    ((intervalPullbackCone_vertex _ _).trans (spaceInfinityVertex_eq_coherent _)) hv
    (kanNativeConeLeg_edge _ _ _ i).symm hr
    (fiberwisePullbackNativeConeHomotopy_apexEdge p f g)
    (intervalPullbackConeKanLeg_edge _ _ i).symm
  have hid : SSet.Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (𝟙 K)).toTruncated = 𝟙 _ := by
    rw [coherentNerveEdge_id, SSet.Edge.toTruncated_id,
      SSet.Truncated.HomotopyCategory.homMk_id]
  rw [hid, Category.comp_id] at hs
  apply spaceInfinity_homotopy_of_homMk_eq
  exact hs.trans (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct (fiberwisePullbackComparisonKanMap p f g)
      (intervalPullbackConeKanLeg (continuousKanMap f) (continuousKanMap g) i)).toTruncated)

end SerrePositivity.InfinityCategories.F2
