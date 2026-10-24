module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInternalHomOpposite
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftFunctorInitial
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeRightOppositeCriterion
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.F1B.Diagrams.OppositeLifting

/-!
概要：標準相対右 Kan 関手は元の相対関手制限に関する相対終対象。
方針：反転後の左の相対始対象性を内部 Hom と相対標的の反転同型で戻す。
規約：相手の関手の普遍性は要求しない。
使われ方：任意の始点から右 Kan 関手へ入る相対写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の相対右 Kan 関手は元の相対制限に関して相対終対象。
方針：左の始点境界充填を相対始対象性へ移し、反転同型の可換正方形で反映する。
規約：δ は充満忠実な inner 単射、U は同値を持ち上げる。
使われ方：右 Kan 関手を終点とする片側の相対写像空間比較。 -/
lemma kanRelativeRightFunctor_relative_terminal {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (s : internalHom.PullbackObjObj δ U) (H : C ⟶ D)
    (hlim : IsRelativeRightKanExtendedFrom U δ H) :
    KanRelativeTerminalVertex s.π (functorVertex H) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have : InnerFibration U := hU.innerFibration
  have hUop : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (SSet.opFunctor.map U) := hU.op
  have : InnerFibration (SSet.opFunctor.map U) := hUop.innerFibration
  have : Quasicategory s.pt := kanRelativeInternalHomTarget_quasicategory U δ s
  let t := Functor.PullbackObjObj.ofHasPullback internalHom
    (SSet.opFunctor.map δ) (SSet.opFunctor.map U)
  have : Quasicategory t.pt := kanRelativeInternalHomTarget_quasicategory _ _ t
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  have : Quasicategory ((internalHom.obj (Opposite.op C.op)).obj D.op) :=
    inferInstanceAs (Quasicategory ((ihom C.op).obj D.op))
  have hx := kanRelativeInitialVertex_of_initialBoundary t.π
    (functorVertex (SSet.opFunctor.map H))
    (kanRelativeLeftFunctor_relative_initialBoundary (SSet.opFunctor.map δ)
      (SerrePositivity.InfinityCategories.F1B.isFullyFaithful_op δ hδ) (SSet.opFunctor.map U) hUop t (SSet.opFunctor.map H)
      ((kanIsRelativeRightKanExtendedFrom_iff_op_left U δ H).1 hlim))
  let a := HomotopyLimits.oppositeInternalHomIso C D
  let b := kanRelativeInternalHomOppositeIso δ U s t
  apply (kanRelativeInitialVertex_iff_of_comparison (SSet.opFunctor.map s.π) t.π
    a.hom b.hom (kanRelativeInternalHomOppositeIso_comparison δ U s t)
    (qCatEquivalenceOfIso a).isQCatEquivalence.isFullyFaithful
    (qCatEquivalenceOfIso b).isQCatEquivalence.isFullyFaithful
    (kanIso_app_surjective a (Opposite.op ⦋0⦌)) (SSet.opObjEquiv.symm (functorVertex H))).2
  exact (congrArg (fun x ↦ KanRelativeInitialVertex t.π x)
    (SerrePositivity.InfinityCategories.F1B.oppositeInternalHom_vertex H)).mpr hx

end SerrePositivity.InfinityCategories.F1B
