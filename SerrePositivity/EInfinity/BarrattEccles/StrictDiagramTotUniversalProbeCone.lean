module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalWeightedCone
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeComparison
public import SerrePositivity.EInfinity.HomotopyWeight.ConePoints

/-!
概要：普遍重み付き錐を元の同じprobeで評価した実錐空間の零単体。
方針：随伴単位へ元のprobe比較を前合成し、元のconePointを使う。
規約：IS-W2 R03の単位則。native切断や極限性をこの段階で主張しない。
使われ方：元の全Hom比較の標準点の追跡。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DiagramModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 元の同じprobe比較が表す普遍右frame錐。 -/
def strictBETotUniversalProbeWeightedCone (F : K ⥤ (operad A).Algebra) :
    HomotopyWeight.framedLimitWeight K ⟶
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj
        (op (framedLimitProbe A ((framedLimitFunctor A K).obj F))) :=
  strictBETotUniversalWeightedCone A K F ≫
    (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).map
      (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F)).op

/-- 同じprobeの普遍錐は元のweightedCotensorHomEquivの同じ比較射の像。 -/
theorem strictBETotUniversalProbeWeightedCone_comparison
    (F : K ⥤ (operad A).Algebra) :
    strictBETotUniversalProbeWeightedCone A K F =
      weightedCotensorHomEquiv A K F (HomotopyWeight.weight K)
        (framedLimitProbe A ((framedLimitFunctor A K).obj F))
        (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F)) :=
  (strictBETotUniversalWeightedCone_precomp A K F _ _).symm

/-- 同じ元のframedLimitConeSpaceの具体的な普遍錐の零単体。 -/
def strictBETotUniversalProbeConePoint (F : K ⥤ (operad A).Algebra) :
    ((framedLimitConeSpace A K ((framedLimitFunctor A K).obj F)).obj F) _⦋0⦌ :=
  HomotopyWeight.conePoint Kᵒᵖᵒᵖ (HomotopyWeight.framedLimitWeight K)
    (strictBETotUniversalProbeWeightedCone A K F)

end SerrePositivity.EInfinity.BarrattEccles
