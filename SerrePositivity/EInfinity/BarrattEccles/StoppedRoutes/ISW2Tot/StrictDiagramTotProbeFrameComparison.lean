module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotFrameHomComparison
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameFamily

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
open _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeFrameModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 全Hom比較の計算対象側は、元の同じ計算対象のright-frame Hom。 -/
def strictBETotFrameHomLeftSourceIso (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((FrameOverFunctor.hom (FrameOverFunctor.resolution (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K))).obj (op (op F))).obj (op Y) ≅
      ((rightFrameHom (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) Y).obj ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)) :=
  (rightFrameHomOpIso (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) Y ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).symm

/-- 元の任意の試験始域の同じprobeを使うと、計算対象側の比較は無条件にホモトピー同値。 -/
theorem strictBETotProbeFrameHomLeft_equivalence (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsSimplicialHomotopyEquivalence
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameHomLeft A K).app (op (op F))).app (op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y))) := by
  haveI := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameHomLeft_equivalence A K F (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y)

/-- 同じ任意の試験始域のprobeで、重み付きframe錐側の比較も同じ射でホモトピー同値。 -/
theorem strictBETotProbeFrameHomRight_equivalence (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsSimplicialHomotopyEquivalence
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameHomRight A K).app (op (op F))).app (op (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y))) := by
  haveI := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameHomRight_equivalence A K F (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
