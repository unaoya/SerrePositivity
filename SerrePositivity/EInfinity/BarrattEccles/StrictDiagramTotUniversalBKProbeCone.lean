module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalProbeCone
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotWeightComparison
public import SerrePositivity.EInfinity.HomotopyWeight.NativeWeightedPointRestriction

/-!
概要：元の普遍probe錐を、一つの指定BK重み比較で同じBK切断の点へ送る。
方針：同じ右frameのHom図式とprobeを保持し、右随伴同型と重み制限で点を追跡する。
規約：IS-W2 R02〜R03の指定点の照合。join錐・極限性はまだ主張しない。
使われ方：全Hom∞比較とnative切断を通る元のTot錐の構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 元の右frameと元のprobeの全Hom係数図式。 -/
abbrev strictBETotProbeCoefficients (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    Kᵒᵖᵒᵖ ⥤ SSet.{u} :=
  (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj (op (framedLimitProbe A Y))

/-- 一つの指定BK比較を前合成した、同じ元の普遍probe錐。 -/
def strictBETotUniversalBKProbeWeightedCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight Kᵒᵖᵒᵖ ⟶
      strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F) :=
  HomotopyWeight.bkFramedWeightComparison K ≫ strictBETotUniversalProbeWeightedCone A K F

/-- 元の普遍錐をBK重みで読んだ、同じnative切断の指定零単体。 -/
def strictBETotUniversalBKProbeConePoint (F : K ⥤ (operad A).Algebra) :
    (weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))) _⦋0⦌ :=
  HomotopyWeight.nativeWeightedPoint Kᵒᵖᵒᵖ (strictBETotUniversalBKProbeWeightedCone A K F)

/-- 元の普遍probe錐の零単体は、指定された二つの実写像で同じBK切断の点へ移る。 -/
theorem strictBETotUniversalBKProbeConePoint_comparison (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsPre (HomotopyWeight.bkFramedWeightComparison K)
      (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
        ((((HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
          (HomotopyWeight.framedLimitWeight K)).hom.app
            (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
              (strictBETotUniversalProbeConePoint A K F)) =
      strictBETotUniversalBKProbeConePoint A K F := by
  change ((weightedSectionsPre (HomotopyWeight.bkFramedWeightComparison K)
    (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
      ((((HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
        (HomotopyWeight.framedLimitWeight K)).hom.app _).app (op ⦋0⦌))
        (HomotopyWeight.conePoint Kᵒᵖᵒᵖ (HomotopyWeight.framedLimitWeight K)
          (strictBETotUniversalProbeWeightedCone A K F))) = _
  rw [HomotopyWeight.coneSpaceNativeSectionsIso_point]
  exact HomotopyWeight.nativeWeightedPoint_pre Kᵒᵖᵒᵖ _ _

end SerrePositivity.EInfinity.BarrattEccles
