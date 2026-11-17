module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotUniversalProbeCone
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotTensorFrameProperties
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameConeClasses

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じBE tensor frameの零次Homが普遍probe錐の同じ標準点に写る。
方針：元のtensorFrameHomIso_pointを同じframe・重み・probe比較で評価。
規約：IS-W2 R03の単位則の特殊化。元の標準点を置き換えない。
使われ方：全Hom比較と指定native制限の標準脚の照合の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.Opposite _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DiagramModel
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotUniversalPointModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 同じ元のprobe比較の零次Homは、普遍重み付き錐の同じ零単体を表す。 -/
theorem strictBETotTensorFrameConeIso_universalPoint
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameConeIso A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).hom.app
      (Opposite.op ⦋0⦌))
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameZeroIso A K).hom.app (op F) ≫
          (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).op) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeConePoint A K F := by
  change (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso Kᵒᵖ
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).hom.app
      (op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)))).app (Opposite.op ⦋0⦌))
        ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameZeroIso Kᵒᵖ
          (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).hom ≫
            (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).op) = _
  have hp := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso_point Kᵒᵖ
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)
    (Y := op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).op
  simp only [Iso.app_hom] at hp
  rw [hp]
  unfold _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeConePoint _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeWeightedCone
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalWeightedCone
  rw [Adjunction.homEquiv_unit]

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
