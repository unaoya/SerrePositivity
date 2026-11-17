module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeSourceFunctor
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitComparison

/-!
概要：元の普遍BK錐への始域の前合成を、元のweighted Hom同値による同じ射の像と合わせる。
方針：全始域の係数同型の自然性と、既存probe比較・weighted Hom同値の始域自然性を合成する。
規約：IS-W2 R02〜R03の既存の単位・始域自然性の法則。元の射f・probeを保持する。
使われ方：元のnative錐の制限と、元の計算対象へのHomの対応の正規化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Opposite
open SerrePositivity.DiagramModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotUniversalSourceNaturalityModel : ModelCategory (operad A).Algebra := modelCategory A

/-- 元の同じ普遍BK錐を、元のfのprobeによる前合成で移す。 -/
def strictBETotBKProbeArrowCone (F : K ⥤ (operad A).Algebra)
    {Y : (operad A).Algebra} (f : Y ⟶ (framedLimitFunctor A K).obj F) :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight
      Kᵒᵖᵒᵖ ⟶ strictBETotProbeRightHomDiagram A K F Y :=
  strictBETotUniversalBKRightHomCone A K F ≫
    (strictBETotProbeRightHomSourceFunctor A K F).map f.op

/-- 元のfから得たBK錐は、元のweighted Hom同値による同じfの像。 -/
theorem strictBETotBKProbeArrowCone_comparison (F : K ⥤ (operad A).Algebra)
    {Y : (operad A).Algebra} (f : Y ⟶ (framedLimitFunctor A K).obj F) :
    strictBETotBKProbeArrowCone A K F f ≫ (strictBETotProbeCoefficientsIso A K F Y).hom =
      HomotopyWeight.bkFramedWeightComparison K ≫
        weightedCotensorHomEquiv A K F (HomotopyWeight.weight K) (framedLimitProbe A Y)
          (framedLimitProbeComparison A Y ≫ f) := by
  let T := (framedLimitFunctor A K).obj F
  have hi : (strictBETotProbeRightHomSourceFunctor A K F).map f.op ≫
      (strictBETotProbeCoefficientsIso A K F Y).hom =
    (strictBETotProbeCoefficientsIso A K F T).hom ≫
      (strictBETotProbeCoefficientsSourceFunctor A K F).map f.op :=
    (strictBETotProbeCoefficientsSourceIso A K F).hom.naturality f.op
  rw [strictBETotBKProbeArrowCone, Category.assoc, hi, ← Category.assoc,
    strictBETotUniversalBKRightHomCone_back, strictBETotUniversalBKProbeWeightedCone,
    Category.assoc, strictBETotUniversalProbeWeightedCone_comparison]
  change HomotopyWeight.bkFramedWeightComparison K ≫
    (weightedCotensorHomEquiv A K F (HomotopyWeight.weight K) (framedLimitProbe A T)
      (framedLimitProbeComparison A T) ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).map
          ((framedLimitProbeFunctor A).map f).op) = _
  rw [← weightedCotensorHomEquiv_precomp]
  have hc (Z : (operad A).Algebra) :
      (framedLimitProbeComparisonNatTrans A).app Z = framedLimitProbeComparison A Z := rfl
  have hn : (framedLimitProbeFunctor A).map f ≫ framedLimitProbeComparison A T =
      framedLimitProbeComparison A Y ≫ f := by
    have h := (framedLimitProbeComparisonNatTrans A).naturality f
    simp only [Functor.id_map, hc] at h
    exact h
  rw [hn]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
