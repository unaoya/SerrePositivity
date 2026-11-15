module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointFirstSpan
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotModelSource
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveTransformationInversion

/-!
概要：全始域・全次数のsource frameの同じaugmentationを、一つの全関手圏で反転する。
方針：元の関手的解消とprobe比較の全自然変換をuncurryし、指定局所化に送る。
規約：IS-W2 R03dの既存の単位・係数移送・反転則。逆を対象ごとに選ばない。
使われ方：両端が変数の屋根比較を構成するための、同じ大域的な逆。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
variable (A : Type u) [CommRing A]
local instance jointAugmentationModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointAugmentationFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 全始域と全source次数の同じ積添字。 -/
abbrev strictBETotJointSourceFrameIndex := AsSmall.{u+1} ((operad A).Algebra × SimplexCategory)

/-- 元のprobeのsource frameを全始域・全次数で評価する。 -/
def strictBETotJointSourceFrameEvaluation :
    strictBETotJointSourceFrameIndex A ⥤ AsSmall.{u+1} (operad A).Algebra :=
  AsSmall.down ⋙ Functor.uncurry.obj ((framedLimitProbeFunctor A) ⋙
    (SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).obj) ⋙ AsSmall.up

/-- 元の始域を全次数で定値にした同じ図式。 -/
def strictBETotJointSourceFrameConstant :
    strictBETotJointSourceFrameIndex A ⥤ AsSmall.{u+1} (operad A).Algebra :=
  AsSmall.down ⋙ Functor.uncurry.obj (Functor.const SimplexCategory) ⋙ AsSmall.up

/-- 同じsource frameのaugmentationと同じprobe比較を合成した全自然変換。 -/
def strictBETotJointSourceFrameAugmentation :
    strictBETotJointSourceFrameEvaluation A ⟶ strictBETotJointSourceFrameConstant A :=
  Functor.whiskerRight
    (Functor.whiskerLeft AsSmall.down (Functor.uncurry.map
      (Functor.whiskerLeft (framedLimitProbeFunctor A)
        (SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).augmentation ≫
      Functor.whiskerRight (framedLimitProbeComparisonNatTrans A) (Functor.const SimplexCategory)))) AsSmall.up

/-- 同じ全augmentationの各成分は、元のモデル弱同値。 -/
theorem strictBETotJointSourceFrameAugmentation_weak (P : strictBETotJointSourceFrameIndex A) :
    weakEquivalences (operad A).Algebra
      (AsSmall.down.map ((strictBETotJointSourceFrameAugmentation A).app P)) := by
  change weakEquivalences (operad A).Algebra
    (((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).augmentation.app
      (framedLimitProbe A (AsSmall.down.obj P).1)).app (AsSmall.down.obj P).2 ≫ framedLimitProbeComparison A (AsSmall.down.obj P).1)
  apply (weakEquivalences (operad A).Algebra).comp_mem
  · exact ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
      (framedLimitProbe A (AsSmall.down.obj P).1)).augmentation_weakEquivalence (AsSmall.down.obj P).2
  · rw [modelCategory_weakEquivalences]
    exact framedLimitProbeComparison_quasiIso A (AsSmall.down.obj P).1

/-- 同じ指定モデル源は、元の全augmentationの辺を反転する。 -/
theorem strictBETotJointSourceFrameAugmentation_inverted (P : strictBETotJointSourceFrameIndex A) :
    IsInvertibleEdge ((nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app P)).map
      (strictBETotModelSource A)).toTruncated := by
  have h := (strictBETotModelSource_isLocalization A).choose
    (show (nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app P)).edge ∈
      SerrePositivity.EInfinity.SimplicialLocalization.weakNerveEdges
        (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
          (operad A).Algebra) from
      ⟨_, _, _, strictBETotJointSourceFrameAugmentation_weak A P, rfl⟩)
  change IsInvertibleEdge (X := CAlg_R A) ((edgeOfSimplex
    (nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app P)).edge).map
      ((SSet.truncation 2).map (strictBETotModelSource A))) at h
  exact (isInvertibleEdge_congr (X := CAlg_R A)
    (e := (edgeOfSimplex
      (nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app P)).edge).map
        ((SSet.truncation 2).map (strictBETotModelSource A)))
    (f := ((nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app P)).map
      (strictBETotModelSource A)).toTruncated) rfl).mp h

/-- 全始域・全次数の同じaugmentation自身の全関手同型。 -/
def strictBETotJointSourceFrameAugmentationIso :
    FunctorIso (nerveMap (strictBETotJointSourceFrameEvaluation A) ≫ strictBETotModelSource A)
      (nerveMap (strictBETotJointSourceFrameConstant A) ≫ strictBETotModelSource A) :=
  nerveTransformationPostIso (strictBETotJointSourceFrameAugmentation A)
    (strictBETotModelSource A) (strictBETotJointSourceFrameAugmentation_inverted A)

end SerrePositivity.EInfinity.BarrattEccles
