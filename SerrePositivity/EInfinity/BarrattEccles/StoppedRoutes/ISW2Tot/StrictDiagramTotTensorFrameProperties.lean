module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotTensorFrame
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitCones

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じBE重み付きendの実tensor frameを、全図式射の族として読む。
方針：既存のframe実現の全関手を標準単体で評価し、同じ零次同型で増大。
規約：IS-W2 R03の既存構成の自然性・単位の法則。重みとframeを変更しない。
使われ方：計算対象のright frameと実重み付き錐空間の同じ全比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra _root_.Opposite
open _root_.SerrePositivity.DiagramModel _root_.SerrePositivity.Reedy
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotTensorPropertiesModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 同じ実tensor frameの各値はReedy cofibrant。 -/
theorem strictBETotTensorFrame_reedyCofibrant (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    reedyLeft simplex (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ)
      (initial.to ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).obj (op F))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame_reedyCofibrant Kᵒᵖ
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => _root_.SerrePositivity.EInfinity.BarrattEccles.rightFrame_cofibrant A (F.obj k.unop))

/-- 同じtensor frameの全単体作用素は元のモデル弱同値。 -/
theorem strictBETotTensorFrame_homotopicallyConstant (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    {n m : SimplexCategory} (α : n ⟶ m) :
    weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).obj (op F)).map α) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame_homotopicallyConstant Kᵒᵖ
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => _root_.SerrePositivity.EInfinity.BarrattEccles.rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => _root_.SerrePositivity.EInfinity.BarrattEccles.rightFrame_homotopicallyConstant A (F.obj k.unop) f) α

/-- 同じ全tensor frameの増大写像は、各次数で元のモデル弱同値。 -/
theorem strictBETotTensorFrameAugmentation_weak
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (n : SimplexCategory) :
    weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameAugmentation A K).app (op F)).app n) := by
  exact (weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ).comp_mem _ _
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrame_homotopicallyConstant A K F (SimplexCategory.const n ⦋0⦌ 0))
    ((weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ).of_isIso
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameZeroIso A K).hom.app (op F)))

/-- 同じtensor frameからの全Homは、元の重み付きframe錐空間そのもの。 -/
def strictBETotTensorFrameConeIso (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).obj (op F))).obj (op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y))) ≅
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSpace A K Y).obj F :=
  (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).app (op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y))

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
