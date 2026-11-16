module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotUniversalWeightedCone
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConePoints

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：普遍重み付き錐を元の同じprobeで評価した実錐空間の零単体。
方針：随伴単位へ元のprobe比較を前合成し、元のconePointを使う。
規約：IS-W2 R03の単位則。native切断や極限性をこの段階で主張しない。
使われ方：元の全Hom比較の標準点の追跡。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.DiagramModel
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 元の同じprobe比較が表す普遍右frame錐。 -/
def strictBETotUniversalProbeWeightedCone (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K ⟶
      (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).obj
        (op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalWeightedCone A K F ≫
    (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).map
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).op

/-- 同じprobeの普遍錐は元のweightedCotensorHomEquivの同じ比較射の像。 -/
theorem strictBETotUniversalProbeWeightedCone_comparison
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeWeightedCone A K F =
      _root_.SerrePositivity.EInfinity.BarrattEccles.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalWeightedCone_precomp A K F _ _).symm

/-- 同じ元のframedLimitConeSpaceの具体的な普遍錐の零単体。 -/
def strictBETotUniversalProbeConePoint (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSpace A K ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).obj F) _⦋0⦌ :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeWeightedCone A K F)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
