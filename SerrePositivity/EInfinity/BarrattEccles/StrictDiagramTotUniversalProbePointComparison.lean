module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalProbeCone
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotTensorFrameProperties
public import SerrePositivity.EInfinity.HomotopyWeight.FrameConeClasses

/-!
概要：同じBE tensor frameの零次Homが普遍probe錐の同じ標準点に写る。
方針：元のtensorFrameHomIso_pointを同じframe・重み・probe比較で評価。
規約：IS-W2 R03の単位則の特殊化。元の標準点を置き換えない。
使われ方：全Hom比較と指定native制限の標準脚の照合の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotUniversalPointModelCategory : ModelCategory (operad A).Algebra :=
  modelCategory A

/-- 同じ元のprobe比較の零次Homは、普遍重み付き錐の同じ零単体を表す。 -/
theorem strictBETotTensorFrameConeIso_universalPoint
    (F : K ⥤ (operad A).Algebra) :
    ((strictBETotTensorFrameConeIso A K F ((framedLimitFunctor A K).obj F)).hom.app
      (Opposite.op ⦋0⦌))
        ((strictBETotTensorFrameZeroIso A K).hom.app (op F) ≫
          (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F)).op) =
      strictBETotUniversalProbeConePoint A K F := by
  change (((HomotopyWeight.tensorFrameHomIso Kᵒᵖ
    (HomotopyWeight.framedLimitWeight K) (rightFrameDiagram A K F)).hom.app
      (op (framedLimitProbe A ((framedLimitFunctor A K).obj F)))).app (Opposite.op ⦋0⦌))
        ((HomotopyWeight.tensorFrameZeroIso Kᵒᵖ
          (HomotopyWeight.framedLimitWeight K) (rightFrameDiagram A K F)).hom ≫
            (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F)).op) = _
  have hp := HomotopyWeight.tensorFrameHomIso_point Kᵒᵖ
    (HomotopyWeight.framedLimitWeight K) (rightFrameDiagram A K F)
    (Y := op (framedLimitProbe A ((framedLimitFunctor A K).obj F)))
    (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F)).op
  simp only [Iso.app_hom] at hp
  rw [hp]
  unfold strictBETotUniversalProbeConePoint strictBETotUniversalProbeWeightedCone
    strictBETotUniversalWeightedCone
  rw [Adjunction.homEquiv_unit]

end SerrePositivity.EInfinity.BarrattEccles
