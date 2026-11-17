module
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimit
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZero

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
local instance strictBETotTensorModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 元の同じ一点重みに標準単体をテンソルする全重み族。 -/
def strictBETotTensorWeights : SimplexCategory ⥤ (Kᵒᵖᵒᵖ ⥤ SSet.{u}) :=
  SSet.stdSimplex ⋙ WeightedCones.tensorDiagram Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)

/-- 同じ実BE計算対象を零次に持つtensor frameの全図式族。 -/
def strictBETotTensorFrameFamily :
    (K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)ᵒᵖ ⥤ SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K ⋙ FrameWeightRealization.family Kᵒᵖ ⋙
    (Functor.whiskeringLeft SimplexCategory (Kᵒᵖᵒᵖ ⥤ SSet.{u})
      (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ).obj (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorWeights K)

/-- 全族の各値は元の同じ実tensor frame。 -/
theorem strictBETotTensorFrameFamily_obj (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).obj (op F) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F) := rfl

/-- 同じ標準零単体の単位則は、全図式射に自然な零次同型を与える。 -/
def strictBETotTensorFrameZeroIso :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K ⋙
      (evaluation SimplexCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ).obj ⦋0⦌ ≅
        _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K :=
  Functor.isoWhiskerLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily A K ⋙ FrameWeightRealization.family Kᵒᵖ)
    ((evaluation (Kᵒᵖᵒᵖ ⥤ SSet.{u}) (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ).mapIso
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)))

/-- 同じ全tensor frameを同じ元の計算対象へ増大する。 -/
def strictBETotTensorFrameAugmentation :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K ⟶
      _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K ⋙ Functor.const SimplexCategory where
  app F :=
    { app n := ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).obj F).map
        (SimplexCategory.const n ⦋0⦌ 0) ≫ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameZeroIso A K).hom.app F
      naturality n m α := by
        change _ ≫ _ = _ ≫ (_ ≫ _)
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
        congr 2 }
  naturality F G f := by
    apply NatTrans.ext
    funext n
    change ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).map f).app n ≫
        (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).obj G).map
          (SimplexCategory.const n ⦋0⦌ 0) ≫ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameZeroIso A K).hom.app G) =
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).obj F).map (SimplexCategory.const n ⦋0⦌ 0) ≫
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameZeroIso A K).hom.app F) ≫ (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K).map f
    rw [← Category.assoc, ← ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).map f).naturality,
      Category.assoc]
    have hz := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameZeroIso A K).hom.naturality f
    change ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K).map f).app ⦋0⦌ ≫
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameZeroIso A K).hom.app G =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameZeroIso A K).hom.app F ≫ (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K).map f at hz
    rw [hz, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
