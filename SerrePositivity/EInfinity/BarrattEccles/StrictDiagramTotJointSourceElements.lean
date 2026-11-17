module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointFirstSpan
public import SerrePositivity.EInfinity.FrameHom.LiftedSourceFrameElements

/-!
概要：元のBEの全source-frame係数を、同じ全要素圏のnative分類へ送る。
方針：元の両変数の第三図式へ検証済みの全係数比較を適用する。
規約：元のprobe・frame・標的置換・全射を保つ。正本Hom∞との照合は別。
使われ方：R03dの同じ全augmentationとtwisted pairingへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]
local instance jointSourceElementsModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourceElementsFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の全probeに同じ関手的source frameを適用した図式。 -/
def strictBETotJointSourceFrame :
    (operad A).Algebra ⥤ SimplexCategory ⥤ (operad A).Algebra :=
  framedLimitProbeFunctor A ⋙
    (SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).obj

/-- 元の第三のHom図式を、同じ全要素係数として記録する。 -/
def strictBETotJointSourceCoefficients : strictBETotJointHomIndex A ⥤ SSet.{u+1} :=
  FrameHom.liftedSourceFrameCoefficients (strictBETotJointSourceFrame A)
    (rightFrameReplacement (rightFrameFamily A))

/-- 同じ全係数は元の第三の図式そのもの。 -/
theorem strictBETotJointSourceCoefficients_eq :
    strictBETotJointSourceCoefficients A =
      AsSmall.down ⋙ strictBETotJointFirstSpanDiagram A 3 := rfl

/-- 元の全source-frameのHom単体の全要素圏。 -/
abbrev StrictBETotJointSourceElements := SimplicialTotalElements (strictBETotJointSourceCoefficients A)

/-- 同じ元の全要素圏から元の両変数の底への射影。 -/
def strictBETotJointSourceElementsProjection :
    StrictBETotJointSourceElements A ⥤ strictBETotJointHomIndex A :=
  simplicialTotalElementsProjection (strictBETotJointSourceCoefficients A)

/-- 元の全要素のラベルを、同じ元のsource-frameの実射へ戻す。 -/
def strictBETotJointSourceElementsDown :=
  FrameHom.liftedSourceFrameElementsDown (strictBETotJointSourceFrame A)
    (rightFrameReplacement (rightFrameFamily A))

/-- 元の第三図式を同じ元の全要素圏のnative全分類へつなぐ。 -/
def strictBETotJointSourceElementsClassificationIso :
    FunctorIso (strictBETotJointFirstSpanCoherent A 3)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj
          (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).hom) :=
  FrameHom.totalElementsNativeClassificationIso (strictBETotJointSourceCoefficients A)

/-- 元の最初の三辺を含むraw Homから、同じ全要素圏のnative全分類への比較。 -/
def strictBETotJointRawSourceElementsClassificationIso :
    FunctorIso (strictBETotJointRawHomCoherent A)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj
          (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).hom) :=
  (strictBETotJointFirstSpanComparison A).trans (strictBETotJointSourceElementsClassificationIso A)
end SerrePositivity.EInfinity.BarrattEccles
