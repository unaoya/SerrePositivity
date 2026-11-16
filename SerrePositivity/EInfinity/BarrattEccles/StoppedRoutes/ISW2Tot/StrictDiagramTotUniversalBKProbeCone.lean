module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotUniversalProbeCone
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotWeightComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedPointRestriction

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の普遍probe錐を、一つの指定BK重み比較で同じBK切断の点へ送る。
方針：同じ右frameのHom図式とprobeを保持し、右随伴同型と重み制限で点を追跡する。
規約：IS-W2 R02〜R03の指定点の照合。join錐・極限性はまだ主張しない。
使われ方：全Hom∞比較とnative切断を通る元のTot錐の構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.DiagramModel
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 元の右frameと元のprobeの全Hom係数図式。 -/
abbrev strictBETotProbeCoefficients (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    Kᵒᵖᵒᵖ ⥤ SSet.{u} :=
  (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).obj (op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y))

/-- 一つの指定BK比較を前合成した、同じ元の普遍probe錐。 -/
def strictBETotUniversalBKProbeWeightedCone (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    bousfieldKanWeight Kᵒᵖᵒᵖ ⟶
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison K ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeWeightedCone A K F

/-- 元の普遍錐をBK重みで読んだ、同じnative切断の指定零単体。 -/
def strictBETotUniversalBKProbeConePoint (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))) _⦋0⦌ :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint Kᵒᵖᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKProbeWeightedCone A K F)

/-- 元の普遍probe錐の零単体は、指定された二つの実写像で同じBK切断の点へ移る。 -/
theorem strictBETotUniversalBKProbeConePoint_comparison (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((weightedSectionsPre (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison K)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
        ((((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
          (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).hom.app
            (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
              (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeConePoint A K F)) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKProbeConePoint A K F := by
  change ((weightedSectionsPre (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison K)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
      ((((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).hom.app _).app (op ⦋0⦌))
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeWeightedCone A K F))) = _
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso_point]
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint_pre Kᵒᵖᵒᵖ _ _

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
