module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedArrowIso
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningOverIso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：通常の Hom の元の圏と実際の twisted arrow の同型を全分類図式の同型へ送る。
方針：既存の同型の四角形の引き戻しの普遍性と、共同 straightening の底変換を合成する。
規約：対象ごとの同型ではなく、同じ全 Hom の底全体の関手同型を与える。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、Corollary 5.6.0.6（Tag 028T）、
HTT 5.1.5.6 の固定 Yoneda の全族比較への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable (C : Type u) [SmallCategory C]

/-- 通常の Hom の元の圏の射影は、実際の twisted arrow の射影と同型なので left fibration。
Kerodon Proposition 8.1.1.10（Tag 03JN）、既存の left fibration の同型移送則。 -/
instance ordinaryHomProjection_leftFibration :
    LeftFibration (nerveMap (ordinaryHomElementsProjection C)) :=
  ⟨(leftFibrations.arrow_mk_iso_iff (ordinaryHomTwistedArrowIso C)).mpr
    (LeftFibration.mem (p := twistedArrowProjection (nerve C)))⟩

/-- 同じ全 Hom の模型比較の四角形は、底の同型に沿う引き戻しである。
Kerodon Proposition 8.1.1.10（Tag 03JN）、既存の同型の四角形の普遍性の法則。 -/
lemma ordinaryHomTwisted_isPullback :
    IsPullback (ordinaryHomTwistedIso C).hom (nerveMap (ordinaryHomElementsProjection C))
      (twistedArrowProjection (nerve C)) (ordinaryHomBaseIso C).hom :=
  IsPullback.of_horiz_isIso ⟨ordinaryHomTwistedIso_projection C⟩

/-- 底を固定すると、同じ Hom の射影は実際の twisted arrow の引き戻しと底上で同型。
Kerodon Proposition 8.1.1.10（Tag 03JN）、同じ引き戻しの指定同型。 -/
def ordinaryHomTwistedPullbackIso :
    Over.mk (nerveMap (ordinaryHomElementsProjection C)) ≅
      Over.mk (pullback.snd (twistedArrowProjection (nerve C)) (ordinaryHomBaseIso C).hom) :=
  Over.isoMk ((ordinaryHomTwisted_isPullback C).isoIsPullback _ _
    (IsPullback.of_hasPullback (twistedArrowProjection (nerve C)) (ordinaryHomBaseIso C).hom))
    (by simp)

local instance : LeftFibration
    (pullback.snd (twistedArrowProjection (nerve C)) (ordinaryHomBaseIso C).hom) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := twistedArrowProjection (nerve C)))⟩

/-- 実際の Hom 分類を底の指定同型で戻すと、元の Hom の元の圏の全分類と関手同型。
Kerodon Proposition 8.1.1.10（Tag 03JN）、Corollary 5.6.0.6（Tag 028T）、
HTT 5.1.5.6。全底の一つの図式の同型であり、対象ごとの比較で代用しない。 -/
def ordinaryHomTwistedClassificationIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (ordinaryHomBaseIso C).hom ≫
        twistedArrowHomInfinity (nerve C))
      (leftStraighteningInfinityDiagram (nerveMap (ordinaryHomElementsProjection C))) :=
  leftStraighteningInfinityDiagram_baseChangeIso (twistedArrowProjection (nerve C))
      (ordinaryHomBaseIso C).hom ≪≫
    (leftStraighteningInfinityDiagram_overIso (nerveMap (ordinaryHomElementsProjection C))
      (pullback.snd (twistedArrowProjection (nerve C)) (ordinaryHomBaseIso C).hom)
      (ordinaryHomTwistedPullbackIso C)).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
