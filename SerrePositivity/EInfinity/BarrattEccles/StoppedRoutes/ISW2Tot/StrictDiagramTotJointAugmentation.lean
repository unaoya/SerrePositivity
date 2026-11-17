module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointFirstSpan
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotModelSource
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveTransformationInversion

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：全始域・全次数のsource frameの同じaugmentationを、一つの全関手圏で反転する。
方針：元の関手的解消とprobe比較の全自然変換をuncurryし、指定局所化に送る。
規約：IS-W2 R03dの既存の単位・係数移送・反転則。逆を対象ごとに選ばない。
使われ方：両端が変数の屋根比較を構成するための、同じ大域的な逆。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
variable (A : Type u) [CommRing A]
local instance jointAugmentationModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointAugmentationFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 全始域と全source次数の同じ積添字。 -/
abbrev strictBETotJointSourceFrameIndex := AsSmall.{u+1} ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra × SimplexCategory)

/-- 元のprobeのsource frameを全始域・全次数で評価する。 -/
def strictBETotJointSourceFrameEvaluation :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  AsSmall.down ⋙ Functor.uncurry.obj ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A) ⋙
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).obj) ⋙ AsSmall.up

/-- 元の始域を全次数で定値にした同じ図式。 -/
def strictBETotJointSourceFrameConstant :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  AsSmall.down ⋙ Functor.uncurry.obj (Functor.const SimplexCategory) ⋙ AsSmall.up

/-- 同じsource frameのaugmentationと同じprobe比較を合成した全自然変換。 -/
def strictBETotJointSourceFrameAugmentation :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameEvaluation A ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameConstant A :=
  Functor.whiskerRight
    (Functor.whiskerLeft AsSmall.down (Functor.uncurry.map
      (Functor.whiskerLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).augmentation ≫
      Functor.whiskerRight (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparisonNatTrans A) (Functor.const SimplexCategory)))) AsSmall.up

/-- 同じ全augmentationの各成分は、元のモデル弱同値。 -/
theorem strictBETotJointSourceFrameAugmentation_weak (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A) :
    weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
      (AsSmall.down.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app P)) := by
  change weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
    (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).augmentation.app
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1)).app (AsSmall.down.obj P).2 ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A (AsSmall.down.obj P).1)
  apply (weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).comp_mem
  · exact ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1)).augmentation_weakEquivalence (AsSmall.down.obj P).2
  · rw [_root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory_weakEquivalences]
    exact _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison_quasiIso A (AsSmall.down.obj P).1

/-- 同じ指定モデル源は、元の全augmentationの辺を反転する。 -/
theorem strictBETotJointSourceFrameAugmentation_inverted (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A) :
    IsInvertibleEdge ((nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app P)).map
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)).toTruncated := by
  have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_isLocalization A).choose
    (show (nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app P)).edge ∈
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges
        (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
          (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) from
      ⟨_, _, _, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation_weak A P, rfl⟩)
  change IsInvertibleEdge (X := _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) ((edgeOfSimplex
    (nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app P)).edge).map
      ((SSet.truncation 2).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) at h
  exact (isInvertibleEdge_congr (X := _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)
    (e := (edgeOfSimplex
      (nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app P)).edge).map
        ((SSet.truncation 2).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)))
    (f := ((nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app P)).map
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)).toTruncated) rfl).mp h

/-- 全始域・全次数の同じaugmentation自身の全関手同型。 -/
def strictBETotJointSourceFrameAugmentationIso :
    FunctorIso (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameEvaluation A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
      (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameConstant A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) :=
  nerveTransformationPostIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation_inverted A)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
