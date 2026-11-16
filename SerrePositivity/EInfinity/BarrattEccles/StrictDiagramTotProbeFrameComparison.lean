module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotFrameHomComparison
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameFamily

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
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeFrameModelCategory : ModelCategory (operad A).Algebra := modelCategory A

/-- 全Hom比較の計算対象側は、元の同じ計算対象のright-frame Hom。 -/
def strictBETotFrameHomLeftSourceIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    ((FrameOverFunctor.hom (FrameOverFunctor.resolution (rightFrameFamily A)
      (framedLimitOpFunctor A K))).obj (op (op F))).obj (op Y) ≅
      ((rightFrameHom (rightFrameFamily A) Y).obj ((framedLimitFunctor A K).obj F)) :=
  (rightFrameHomOpIso (rightFrameFamily A) Y ((framedLimitFunctor A K).obj F)).symm

/-- 元の任意の試験始域の同じprobeを使うと、計算対象側の比較は無条件にホモトピー同値。 -/
theorem strictBETotProbeFrameHomLeft_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomLeft A K).app (op (op F))).app (op (framedLimitProbe A Y))) := by
  haveI := framedLimitProbe_cofibrant A Y
  exact strictBETotFrameHomLeft_equivalence A K F (framedLimitProbe A Y)

/-- 同じ任意の試験始域のprobeで、重み付きframe錐側の比較も同じ射でホモトピー同値。 -/
theorem strictBETotProbeFrameHomRight_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomRight A K).app (op (op F))).app (op (framedLimitProbe A Y))) := by
  haveI := framedLimitProbe_cofibrant A Y
  exact strictBETotFrameHomRight_equivalence A K F (framedLimitProbe A Y)

end SerrePositivity.EInfinity.BarrattEccles
