module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightRestrictionOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftRestrictionTheorem
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightRestrictionExistence

/-!
概要：元の相対右 Kan 関手の全部分圏からの制限の充満忠実性と自明 Kan 性。
方針：左の正次元境界充填を反転で移し、厳密な相対存在による頂点全射性を合わせる。
規約：局所相対極限の存在は充満忠実性の仮定に含めない。
使われ方：元の右 Kan 関手の coherent な選択の制限定理。

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

/-- 概要：元の相対右 Kan 制限は正次元の全境界を持ち上げる。
方針：左の充満忠実な inner 制限の境界充填を二つの反転同型で移す。
規約：δ は充満忠実な inner 単射、U は同値を持ち上げる。
使われ方：右の写像空間比較と後の頂点全射性との合流。 -/
lemma kanRelativeRightKanRestriction_boundary_succ {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U) (n : ℕ) :
    HasLiftingProperty (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction U δ s) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have : InnerFibration U := hU.innerFibration
  let t := Functor.PullbackObjObj.ofHasPullback internalHom
    (SSet.opFunctor.map δ) (SSet.opFunctor.map U)
  have hUop : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (SSet.opFunctor.map U) := hU.op
  have : InnerFibration (SSet.opFunctor.map U) := hUop.innerFibration
  have : Quasicategory t.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory _ _ t
  have : Quasicategory
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams (SSet.opFunctor.map U) (SSet.opFunctor.map δ) : SSet.{u}) :=
    inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeLeftKanVertex (SSet.opFunctor.map U) (SSet.opFunctor.map δ)) : SSet.{u}))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_innerFibration
    (SSet.opFunctor.map U) hUop (SSet.opFunctor.map δ) t
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_isFullyFaithful
    (SSet.opFunctor.map U) hUop (SSet.opFunctor.map δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isFullyFaithful_op δ hδ) t
  let e : Arrow.mk (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction U δ s)) ≅
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction (SSet.opFunctor.map U)
        (SSet.opFunctor.map δ) t) :=
    Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanDiagramsOppositeIso U δ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomOppositeIso δ U s t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction_opposite_square U δ s t)
  have ho := (HasLiftingProperty.iff_of_arrow_iso_right (boundary (n + 1)).ι e).mpr
    (hf.hasLiftingProperty_boundary_succ n)
  let eb : Arrow.mk (boundary (n + 1)).ι ≅
      Arrow.mk (SSet.opFunctor.map (boundary (n + 1)).ι) :=
    Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso (n + 1)) (stdSimplex.opIso ⦋n + 1⦌).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.boundaryReverseIso_hom_ι (n + 1))
  exact (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence
    (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction U δ s)).mp
    ((HasLiftingProperty.iff_of_arrow_iso_left eb _).mp ho)

/-- 概要：元の相対右 Kan 関手の全部分圏からの相対制限は充満忠実。
方針：正次元境界充填から全ての指定 pinched 比較の同値を得る。
規約：標準局所相対極限の存在は不要。
使われ方：元の右 Kan 関手全体の写像空間の普遍性。 -/
lemma kanRelativeRightKanRestriction_isFullyFaithful {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction U δ s) := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory U _ s
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanDiagrams U δ : SSet.{u}) :=
    inferInstanceAs (Quasicategory
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeRightKanVertex U δ) : SSet.{u}))
  intro x y
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction U δ s) x y
  intro n a b _ sq
  have := kanRelativeRightKanRestriction_boundary_succ U hU δ hδ s n
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 概要：標準局所相対極限が存在すれば元の相対右 Kan 制限は自明 Kan。
方針：充満忠実性と inner 性に、元と底を厳密に保つ存在による頂点全射性を合わせる。
規約：δ は充満忠実な inner 単射、U は同値を持ち上げる。
使われ方：元の相対 Kan 関手の coherent な選択と制限の可縮な fiber。 -/
lemma kanRelativeRightKanRestriction_trivialKanFibration {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U)
    (hlocal : ∀ (F₀ : K ⟶ D) (H₀ : C ⟶ E), F₀ ≫ U = δ ≫ H₀ →
      ∀ c : C _⦋0⦌, ∃ z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram δ F₀ c),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone U z ∧ z.val ≫ U = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ H₀ c).val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction U δ s) := by
  have : InnerFibration U := hU.innerFibration
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction_innerFibration U hU δ s
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory U _ s
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanDiagrams U δ : SSet.{u}) :=
    inferInstanceAs (Quasicategory
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeRightKanVertex U δ) : SSet.{u}))
  have hf := kanRelativeRightKanRestriction_isFullyFaithful U hU δ hδ s
  exact hf.trivialKanFibration_of_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightKanRestriction_surjective U hU δ hδ s hlocal)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
