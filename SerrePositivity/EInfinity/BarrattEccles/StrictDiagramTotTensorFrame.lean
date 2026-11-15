module
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimit
public import SerrePositivity.EInfinity.HomotopyWeight.TensorPiZero

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
local instance strictBETotTensorModelCategory : ModelCategory (operad A).Algebra := modelCategory A

/-- 元の同じ一点重みに標準単体をテンソルする全重み族。 -/
def strictBETotTensorWeights : SimplexCategory ⥤ (Kᵒᵖᵒᵖ ⥤ SSet.{u}) :=
  SSet.stdSimplex ⋙ WeightedCones.tensorDiagram Kᵒᵖᵒᵖ (HomotopyWeight.framedLimitWeight K)

/-- 同じ実BE計算対象を零次に持つtensor frameの全図式族。 -/
def strictBETotTensorFrameFamily :
    (K ⥤ (operad A).Algebra)ᵒᵖ ⥤ SimplexCategory ⥤ (operad A).Algebraᵒᵖ :=
  rightFrameDiagramFamily A K ⋙ FrameWeightRealization.family Kᵒᵖ ⋙
    (Functor.whiskeringLeft SimplexCategory (Kᵒᵖᵒᵖ ⥤ SSet.{u})
      (operad A).Algebraᵒᵖ).obj (strictBETotTensorWeights K)

/-- 全族の各値は元の同じ実tensor frame。 -/
theorem strictBETotTensorFrameFamily_obj (F : K ⥤ (operad A).Algebra) :
    (strictBETotTensorFrameFamily A K).obj (op F) =
      HomotopyWeight.tensorFrame Kᵒᵖ (HomotopyWeight.framedLimitWeight K)
        (rightFrameDiagram A K F) := rfl

/-- 同じ標準零単体の単位則は、全図式射に自然な零次同型を与える。 -/
def strictBETotTensorFrameZeroIso :
    strictBETotTensorFrameFamily A K ⋙
      (evaluation SimplexCategory (operad A).Algebraᵒᵖ).obj ⦋0⦌ ≅
        framedLimitOpFunctor A K :=
  Functor.isoWhiskerLeft (rightFrameDiagramFamily A K ⋙ FrameWeightRealization.family Kᵒᵖ)
    ((evaluation (Kᵒᵖᵒᵖ ⥤ SSet.{u}) (operad A).Algebraᵒᵖ).mapIso
      (HomotopyWeight.zeroTensorWeightIso Kᵒᵖᵒᵖ (HomotopyWeight.framedLimitWeight K)))

/-- 同じ全tensor frameを同じ元の計算対象へ増大する。 -/
def strictBETotTensorFrameAugmentation :
    strictBETotTensorFrameFamily A K ⟶
      framedLimitOpFunctor A K ⋙ Functor.const SimplexCategory where
  app F :=
    { app n := ((strictBETotTensorFrameFamily A K).obj F).map
        (SimplexCategory.const n ⦋0⦌ 0) ≫ (strictBETotTensorFrameZeroIso A K).hom.app F
      naturality n m α := by
        change _ ≫ _ = _ ≫ (_ ≫ _)
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
        congr 2 }
  naturality F G f := by
    apply NatTrans.ext
    funext n
    change ((strictBETotTensorFrameFamily A K).map f).app n ≫
        (((strictBETotTensorFrameFamily A K).obj G).map
          (SimplexCategory.const n ⦋0⦌ 0) ≫ (strictBETotTensorFrameZeroIso A K).hom.app G) =
      (((strictBETotTensorFrameFamily A K).obj F).map (SimplexCategory.const n ⦋0⦌ 0) ≫
        (strictBETotTensorFrameZeroIso A K).hom.app F) ≫ (framedLimitOpFunctor A K).map f
    rw [← Category.assoc, ← ((strictBETotTensorFrameFamily A K).map f).naturality,
      Category.assoc]
    have hz := (strictBETotTensorFrameZeroIso A K).hom.naturality f
    change ((strictBETotTensorFrameFamily A K).map f).app ⦋0⦌ ≫
      (strictBETotTensorFrameZeroIso A K).hom.app G =
      (strictBETotTensorFrameZeroIso A K).hom.app F ≫ (framedLimitOpFunctor A K).map f at hz
    rw [hz, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
