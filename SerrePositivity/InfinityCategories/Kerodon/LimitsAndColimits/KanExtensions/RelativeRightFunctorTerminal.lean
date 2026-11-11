module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeInternalHomOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftFunctorInitial
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightOppositeCriterion
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeLifting

/-!
概要：標準相対右 Kan 関手は元の相対関手制限に関する相対終対象。
方針：反転後の左の相対始対象性を内部 Hom と相対標的の反転同型で戻す。
規約：相手の関手の普遍性は要求しない。
使われ方：任意の始点から右 Kan 関手へ入る相対写像空間の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：元の相対右 Kan 関手は元の相対制限に関して相対終対象。
方針：左の始点境界充填を相対始対象性へ移し、反転同型の可換正方形で反映する。
規約：δ は充満忠実な inner 単射、U は同値を持ち上げる。
使われ方：右 Kan 関手を終点とする片側の相対写像空間比較。 -/
lemma kanRelativeRightFunctor_relative_terminal {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (s : internalHom.PullbackObjObj δ U) (H : C ⟶ D)
    (hlim : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U δ H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have : InnerFibration U := hU.innerFibration
  have hUop : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (SSet.opFunctor.map U) := hU.op
  have : InnerFibration (SSet.opFunctor.map U) := hUop.innerFibration
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory U δ s
  let t := Functor.PullbackObjObj.ofHasPullback internalHom
    (SSet.opFunctor.map δ) (SSet.opFunctor.map U)
  have : Quasicategory t.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory _ _ t
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  have : Quasicategory ((internalHom.obj (Opposite.op C.op)).obj D.op) :=
    inferInstanceAs (Quasicategory ((ihom C.op).obj D.op))
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_of_initialBoundary t.π
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.opFunctor.map H))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftFunctor_relative_initialBoundary (SSet.opFunctor.map δ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isFullyFaithful_op δ hδ) (SSet.opFunctor.map U) hUop t (SSet.opFunctor.map H)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeRightKanExtendedFrom_iff_op_left U δ H).1 hlim))
  let a := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso C D
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomOppositeIso δ U s t
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInitialVertex_iff_of_comparison (SSet.opFunctor.map s.π) t.π
    a.hom b.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomOppositeIso_comparison δ U s t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso a).isQCatEquivalence.isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso b).isQCatEquivalence.isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIso_app_surjective a (Opposite.op ⦋0⦌)) (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H))).2
  exact (congrArg (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex t.π x)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.oppositeInternalHom_vertex H)).mpr hx

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
