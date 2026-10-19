module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeRightRestrictionOpposite
public import SerrePositivity.InfinityCategories.F1B.KanRelativeLeftRestrictionTheorem
public import SerrePositivity.InfinityCategories.F1B.KanOppositeLifting

/-!
概要：元の相対右 Kan 関手の全部分圏からの制限の充満忠実性。
方針：反転の可換正方形で左の正次元境界充填を移し、指定 pinched 比較を判定する。
規約：局所相対極限の存在は充満忠実性の仮定に含めない。
使われ方：元の右 Kan 関手の coherent な選択の制限定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の相対右 Kan 制限は正次元の全境界を持ち上げる。
方針：左の充満忠実な inner 制限の境界充填を二つの反転同型で移す。
規約：δ は充満忠実な inner 単射、U は同値を持ち上げる。
使われ方：右の写像空間比較と後の頂点全射性との合流。 -/
lemma kanRelativeRightKanRestriction_boundary_succ {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U) (n : ℕ) :
    HasLiftingProperty (boundary (n + 1)).ι (kanRelativeRightKanRestriction U δ s) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have : InnerFibration U := hU.innerFibration
  let t := Functor.PullbackObjObj.ofHasPullback internalHom
    (SSet.opFunctor.map δ) (SSet.opFunctor.map U)
  have hUop : KanEquivalenceLifting (SSet.opFunctor.map U) := hU.op
  have : InnerFibration (SSet.opFunctor.map U) := hUop.innerFibration
  have : Quasicategory t.pt := kanRelativeInternalHomTarget_quasicategory _ _ t
  have : Quasicategory
      (kanRelativeLeftKanDiagrams (SSet.opFunctor.map U) (SSet.opFunctor.map δ) : SSet.{u}) :=
    inferInstanceAs (Quasicategory (fullSubcomplexOnVertices _
      (KanRelativeLeftKanVertex (SSet.opFunctor.map U) (SSet.opFunctor.map δ)) : SSet.{u}))
  have := kanRelativeLeftKanRestriction_innerFibration
    (SSet.opFunctor.map U) hUop (SSet.opFunctor.map δ) t
  have hf := kanRelativeLeftKanRestriction_isFullyFaithful
    (SSet.opFunctor.map U) hUop (SSet.opFunctor.map δ) (kanIsFullyFaithful_op δ hδ) t
  let e : Arrow.mk (SSet.opFunctor.map (kanRelativeRightKanRestriction U δ s)) ≅
      Arrow.mk (kanRelativeLeftKanRestriction (SSet.opFunctor.map U)
        (SSet.opFunctor.map δ) t) :=
    Arrow.isoMk (kanRelativeRightKanDiagramsOppositeIso U δ)
      (kanRelativeInternalHomOppositeIso δ U s t)
      (kanRelativeRightKanRestriction_opposite_square U δ s t)
  have ho := (HasLiftingProperty.iff_of_arrow_iso_right (boundary (n + 1)).ι e).mpr
    (hf.hasLiftingProperty_boundary_succ n)
  let eb : Arrow.mk (boundary (n + 1)).ι ≅
      Arrow.mk (SSet.opFunctor.map (boundary (n + 1)).ι) :=
    Arrow.isoMk (boundaryReverseIso (n + 1)) (stdSimplex.opIso ⦋n + 1⦌).symm
      (boundaryReverseIso_hom_ι (n + 1))
  exact (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence
    (boundary (n + 1)).ι (kanRelativeRightKanRestriction U δ s)).mp
    ((HasLiftingProperty.iff_of_arrow_iso_left eb _).mp ho)

/-- 概要：元の相対右 Kan 関手の全部分圏からの相対制限は充満忠実。
方針：正次元境界充填から全ての指定 pinched 比較の同値を得る。
規約：標準局所相対極限の存在は不要。
使われ方：元の右 Kan 関手全体の写像空間の普遍性。 -/
lemma kanRelativeRightKanRestriction_isFullyFaithful {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U) :
    IsFullyFaithful (kanRelativeRightKanRestriction U δ s) := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory s.pt := kanRelativeInternalHomTarget_quasicategory U _ s
  have : Quasicategory (kanRelativeRightKanDiagrams U δ : SSet.{u}) :=
    inferInstanceAs (Quasicategory
      (fullSubcomplexOnVertices _ (KanRelativeRightKanVertex U δ) : SSet.{u}))
  intro x y
  apply kanPinchedHomMap_equivalence_of_initialBoundary (kanRelativeRightKanRestriction U δ s) x y
  intro n a b _ sq
  have := kanRelativeRightKanRestriction_boundary_succ U hU δ hδ s n
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories.F1B
