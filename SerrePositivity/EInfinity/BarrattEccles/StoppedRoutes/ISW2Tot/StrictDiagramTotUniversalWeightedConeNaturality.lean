module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotUniversalWeightedCone

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じ普遍重み付き錐の全BE図式射に対する自然性。
方針：元の全frame族の対象表示と計算対象の反対表示を先に照合し、既存単位則を適用。
規約：IS-W2 R02の単位・自然性の証明分割。計算上限は変えない。
使われ方：指定native全錐族の標準点と全図式射の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.DiagramModel
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 全frame族の評価は元の同じ各図式のright frame。 -/
theorem strictBETotFrameDiagram_obj (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K).obj (op F) = _root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F := rfl

/-- 同じ計算対象の反対は、元の全frame族を同じ重みで実現した対象。 -/
theorem strictBETotFunctor_obj_op (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    op ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F) =
      (FrameWeightRealization.functor Kᵒᵖ
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K).obj (op F))).obj
          (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) := rfl

/-- 元の全図式射による普遍錐の二つの像は、全重みの自然変換として等しい。 -/
theorem strictBETotUniversalWeightedCone_naturality
    {F G : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : F ⟶ G) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalWeightedCone A K F ≫
      ((FrameWeightRealization.homFamily Kᵒᵖ).map
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K).map f.op).op).app
          (op ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalWeightedCone A K G ≫
        (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K G)).map
          (((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).map f).op) := by
  have h := FrameWeightRealization.unit_frame_naturality Kᵒᵖ
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K).map f.op) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
  simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalWeightedCone, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFunctor_map_op,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFunctor_obj_op, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameDiagram_obj] using h

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
