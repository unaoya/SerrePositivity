module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotBKSections
public import SerrePositivity.EInfinity.HomotopyWeight.NativeWeightedPointMap

/-!
概要：元の右frame Hom係数と、全Hom∞比較の入口の同じrightFrameHom図式を全自然に合わせる。
方針：各射をopにする既存のrightFrameHomOpIsoを、元の全図式の射に沿って束ねる。
規約：IS-W2 R02〜R03の係数移送則。pointwiseな同値を自然性の代わりにしない。
使われ方：同じBK普遍錐を全Hom∞比較へ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeCoefficientComparisonModel : ModelCategory (operad A).Algebra := modelCategory A

/-- 元の二重反対添字で、同じprobeから全right frameへのHomを集める。 -/
def strictBETotProbeRightHomDiagram (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    Kᵒᵖᵒᵖ ⥤ SSet.{u} :=
  (opOpEquivalence K).functor ⋙ F ⋙ rightFrameHom (rightFrameFamily A) (framedLimitProbe A Y)

/-- 既存の反対圏Homの同型は、同じ元の全添字図式について自然同型。 -/
def strictBETotProbeCoefficientsIso (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    strictBETotProbeRightHomDiagram A K F Y ≅ strictBETotProbeCoefficients A K F Y :=
  NatIso.ofComponents
    (fun i => rightFrameHomOpIso (rightFrameFamily A) (framedLimitProbe A Y) (F.obj i.unop.unop))
    (by
      intro i j f
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro g
      rfl)

/-- 同じ指定BK普遍錐を全rightFrameHom図式へ送った自然変換。 -/
def strictBETotUniversalBKRightHomCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight Kᵒᵖᵒᵖ ⟶
      strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F) :=
  strictBETotUniversalBKProbeWeightedCone A K F ≫
    (strictBETotProbeCoefficientsIso A K F ((framedLimitFunctor A K).obj F)).inv

/-- 同じ係数同型で戻すと、元の指定BK普遍錐そのものに戻る。 -/
theorem strictBETotUniversalBKRightHomCone_back (F : K ⥤ (operad A).Algebra) :
    strictBETotUniversalBKRightHomCone A K F ≫
      (strictBETotProbeCoefficientsIso A K F ((framedLimitFunctor A K).obj F)).hom =
        strictBETotUniversalBKProbeWeightedCone A K F := by
  rw [strictBETotUniversalBKRightHomCone, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 全rightFrameHom図式へ送った、同じ指定BK切断の零単体。 -/
def strictBETotUniversalBKRightHomPoint (F : K ⥤ (operad A).Algebra) :
    (weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))) _⦋0⦌ :=
  HomotopyWeight.nativeWeightedPoint Kᵒᵖᵒᵖ (strictBETotUniversalBKRightHomCone A K F)

/-- 同じ係数同型は、元の指定BK点を全rightFrameHom図式の同じ点へ運ぶ。 -/
theorem strictBETotUniversalBKRightHomPoint_comparison (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsMap (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeCoefficientsIso A K F ((framedLimitFunctor A K).obj F)).inv).app (op ⦋0⦌))
        (strictBETotUniversalBKProbeConePoint A K F) = strictBETotUniversalBKRightHomPoint A K F := by
  exact HomotopyWeight.nativeWeightedPoint_map Kᵒᵖᵒᵖ _ _

end SerrePositivity.EInfinity.BarrattEccles
