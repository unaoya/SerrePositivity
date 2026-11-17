module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotTensorFrameProperties
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameComparison

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
local instance strictBETotFrameHomModelCategory : ModelCategory (operad A).Algebra := modelCategory A

/-- 元の計算対象のright frameと同じ実tensor frameを比較する共通の全族。 -/
abbrev strictBETotFrameCommonFamily :=
  FrameOverFunctor.commonObj (rightFrameFactorization A) (rightFrameFamily A)
    (framedLimitOpFunctor A K) (strictBETotTensorFrameFamily A K)
    (strictBETotTensorFrameAugmentation A K)

/-- 同じ計算対象のright frameから共通frameへの全二変数Hom比較。 -/
def strictBETotFrameHomLeft :
    FrameOverFunctor.hom (FrameOverFunctor.resolution (rightFrameFamily A)
      (framedLimitOpFunctor A K)) ⟶ FrameOverFunctor.hom (strictBETotFrameCommonFamily A K) :=
  FrameOverFunctor.homLeft (rightFrameFactorization A) (rightFrameFamily A)
    (framedLimitOpFunctor A K) (strictBETotTensorFrameFamily A K)
    (strictBETotTensorFrameAugmentation A K)

/-- 同じ実tensor frameから共通frameへの全二変数Hom比較。 -/
def strictBETotFrameHomRight :
    FrameOverFunctor.hom (strictBETotTensorFrameFamily A K) ⟶
      FrameOverFunctor.hom (strictBETotFrameCommonFamily A K) :=
  FrameOverFunctor.homRight (rightFrameFactorization A) (rightFrameFamily A)
    (framedLimitOpFunctor A K) (strictBETotTensorFrameFamily A K)
    (strictBETotTensorFrameAugmentation A K)

local instance strictBETotFrameHomFibrantOp (Y : (operad A).Algebra) [IsCofibrant Y] : IsFibrant (op Y) := by
  exact (isFibrant_iff_of_isTerminal (initial.to Y).op initialIsInitial.op).mpr inferInstance

/-- 同じ計算対象のright frameからの実比較は、同じ射でホモトピー同値。 -/
theorem strictBETotFrameHomLeft_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) [IsCofibrant Y] :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomLeft A K).app (op (op F))).app (op Y)) :=
  fixedFrameOverFunctor_homLeft_homotopyEquivalence
    (rightFrameFactorization A) (rightFrameFamily A) (framedLimitOpFunctor A K)
    (strictBETotTensorFrameFamily A K) (strictBETotTensorFrameAugmentation A K)
    (fun F n => strictBETotTensorFrameAugmentation_weak A K F.unop n) (op (op F)) (op Y)

/-- 同じ実tensor frameからの実比較も、同じ射でホモトピー同値。 -/
theorem strictBETotFrameHomRight_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) [IsCofibrant Y] :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomRight A K).app (op (op F))).app (op Y)) :=
  fixedFrameOverFunctor_homRight_homotopyEquivalence
    (rightFrameFactorization A) (rightFrameFamily A) (framedLimitOpFunctor A K)
    (strictBETotTensorFrameFamily A K) (strictBETotTensorFrameAugmentation A K)
    (fun F n => strictBETotTensorFrameAugmentation_weak A K F.unop n)
    (fun F => strictBETotTensorFrame_reedyCofibrant A K F.unop)
    (fun F _ _ α => strictBETotTensorFrame_homotopicallyConstant A K F.unop α)
    (op (op F)) (op Y)

end SerrePositivity.EInfinity.BarrattEccles
