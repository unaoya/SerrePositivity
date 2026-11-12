module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeVertexFiberLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceFiberDiagramChange
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.RelativeInitialEndpoint

/-!
概要：相対始点境界充填から出る写像空間の制限の普遍性。
方針：相対 coslice の端点比較の自明性を固定終点の fiber へ制限し、右 pinched 模型へ移す。
規約：写像空間の同値性を公理や新しい仮定として導入しない。
使われ方：点ごとの Kan 条件から大域的な関手の Hom 普遍性を得る。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：相対始点境界を充填する点からの coslice の固定終点の後合成は自明 Kan fibration。
方針：coslice の端点比較の全境界充填を頂点 fiber の比較へ制限する。
規約：quasicategory 性と inner fibration 性はこの結論には不要。
使われ方：相対始対象から出る写像空間の比較。 -/
lemma coslicePostcompFiberMap_trivialKanFibration_of_initialBoundary {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (SSet.yonedaEquiv a)) (y : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap a p y) := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap a p) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting a p ha
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.lift (f := p) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) rfl) := ht
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeVertexFiberMap_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) p rfl y

/-- 概要：相対始点境界を充填する点からの右 pinched 写像空間の比較はホモトピー同値。
方針：固定終点の coslice の後合成の自明性を既存の写像空間の模型比較で右模型へ移す。
規約：始域と標的は quasicategory、p の充填性は要求しない。
使われ方：局所の Kan 条件から関手圏の大域的な射の普遍性へ進む。 -/
lemma pinchedHomMap_equivalence_of_initialBoundary {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) (x y : E _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap (SSet.yonedaEquiv.symm x) p y) :=
    coslicePostcompFiberMap_trivialKanFibration_of_initialBoundary _ p
      (by rw [Equiv.apply_symm_apply]; exact hx) y
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coslicePostcompFiberMap_equivalence_iff_pinchedHomMap
    (SSet.yonedaEquiv.symm x) p y).1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _)
  have hx' : SSet.yonedaEquiv (SSet.yonedaEquiv.symm x) = x := SSet.yonedaEquiv.apply_symm_apply x
  rw [hx'] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
