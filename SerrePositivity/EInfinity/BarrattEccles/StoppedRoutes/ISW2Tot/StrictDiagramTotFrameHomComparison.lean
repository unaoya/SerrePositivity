module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotTensorFrameProperties
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameComparison

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
local instance strictBETotFrameHomModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 元の計算対象のright frameと同じ実tensor frameを比較する共通の全族。 -/
abbrev strictBETotFrameCommonFamily :=
  FrameOverFunctor.commonObj (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFactorization A) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameAugmentation A K)

/-- 同じ計算対象のright frameから共通frameへの全二変数Hom比較。 -/
def strictBETotFrameHomLeft :
    FrameOverFunctor.hom (FrameOverFunctor.resolution (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K)) ⟶ FrameOverFunctor.hom (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameCommonFamily A K) :=
  FrameOverFunctor.homLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFactorization A) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameAugmentation A K)

/-- 同じ実tensor frameから共通frameへの全二変数Hom比較。 -/
def strictBETotFrameHomRight :
    FrameOverFunctor.hom (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K) ⟶
      FrameOverFunctor.hom (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameCommonFamily A K) :=
  FrameOverFunctor.homRight (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFactorization A) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameAugmentation A K)

local instance strictBETotFrameHomFibrantOp (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) [IsCofibrant Y] : IsFibrant (op Y) := by
  exact (isFibrant_iff_of_isTerminal (initial.to Y).op initialIsInitial.op).mpr inferInstance

/-- 同じ計算対象のright frameからの実比較は、同じ射でホモトピー同値。 -/
theorem strictBETotFrameHomLeft_equivalence (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) [IsCofibrant Y] :
    IsSimplicialHomotopyEquivalence
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameHomLeft A K).app (op (op F))).app (op Y)) :=
  fixedFrameOverFunctor_homLeft_homotopyEquivalence
    (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFactorization A) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameAugmentation A K)
    (fun F n => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameAugmentation_weak A K F.unop n) (op (op F)) (op Y)

/-- 同じ実tensor frameからの実比較も、同じ射でホモトピー同値。 -/
theorem strictBETotFrameHomRight_equivalence (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) [IsCofibrant Y] :
    IsSimplicialHomotopyEquivalence
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameHomRight A K).app (op (op F))).app (op Y)) :=
  fixedFrameOverFunctor_homRight_homotopyEquivalence
    (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFactorization A) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor A K)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameFamily A K) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameAugmentation A K)
    (fun F n => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrameAugmentation_weak A K F.unop n)
    (fun F => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrame_reedyCofibrant A K F.unop)
    (fun F _ _ α => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTensorFrame_homotopicallyConstant A K F.unop α)
    (op (op F)) (op Y)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
