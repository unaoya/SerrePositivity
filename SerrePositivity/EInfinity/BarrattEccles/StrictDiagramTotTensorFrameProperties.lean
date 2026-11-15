module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotTensorFrame
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitCones

/-!
概要：同じBE重み付きendの実tensor frameを、全図式射の族として読む。
方針：既存のframe実現の全関手を標準単体で評価し、同じ零次同型で増大。
規約：IS-W2 R03の既存構成の自然性・単位の法則。重みとframeを変更しない。
使われ方：計算対象のright frameと実重み付き錐空間の同じ全比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomotopicalAlgebra Opposite
open SerrePositivity.DiagramModel SerrePositivity.Reedy
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotTensorPropertiesModelCategory : ModelCategory (operad A).Algebra := modelCategory A

/-- 同じ実tensor frameの各値はReedy cofibrant。 -/
theorem strictBETotTensorFrame_reedyCofibrant (F : K ⥤ (operad A).Algebra) :
    reedyLeft simplex (cofibrations (operad A).Algebraᵒᵖ)
      (initial.to ((strictBETotTensorFrameFamily A K).obj (op F))) :=
  HomotopyWeight.tensorFrame_reedyCofibrant Kᵒᵖ
    (HomotopyWeight.framedLimitWeight K) (rightFrameDiagram A K F)
    (HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => rightFrame_cofibrant A (F.obj k.unop))

/-- 同じtensor frameの全単体作用素は元のモデル弱同値。 -/
theorem strictBETotTensorFrame_homotopicallyConstant (F : K ⥤ (operad A).Algebra)
    {n m : SimplexCategory} (α : n ⟶ m) :
    weakEquivalences (operad A).Algebraᵒᵖ
      (((strictBETotTensorFrameFamily A K).obj (op F)).map α) :=
  HomotopyWeight.tensorFrame_homotopicallyConstant Kᵒᵖ
    (HomotopyWeight.framedLimitWeight K) (rightFrameDiagram A K F)
    (HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => rightFrame_homotopicallyConstant A (F.obj k.unop) f) α

/-- 同じ全tensor frameの増大写像は、各次数で元のモデル弱同値。 -/
theorem strictBETotTensorFrameAugmentation_weak
    (F : K ⥤ (operad A).Algebra) (n : SimplexCategory) :
    weakEquivalences (operad A).Algebraᵒᵖ
      (((strictBETotTensorFrameAugmentation A K).app (op F)).app n) := by
  exact (weakEquivalences (operad A).Algebraᵒᵖ).comp_mem _ _
    (strictBETotTensorFrame_homotopicallyConstant A K F (SimplexCategory.const n ⦋0⦌ 0))
    ((weakEquivalences (operad A).Algebraᵒᵖ).of_isIso
      ((strictBETotTensorFrameZeroIso A K).hom.app (op F)))

/-- 同じtensor frameからの全Homは、元の重み付きframe錐空間そのもの。 -/
def strictBETotTensorFrameConeIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
      ((strictBETotTensorFrameFamily A K).obj (op F))).obj (op (framedLimitProbe A Y))) ≅
        (framedLimitConeSpace A K Y).obj F :=
  (HomotopyWeight.tensorFrameHomIso Kᵒᵖ (HomotopyWeight.framedLimitWeight K)
    (rightFrameDiagram A K F)).app (op (framedLimitProbe A Y))

end SerrePositivity.EInfinity.BarrattEccles
