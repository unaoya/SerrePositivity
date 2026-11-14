module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftFunctorInitial
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftRestrictionExistence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary

/-!
概要：元の相対左 Kan 関手の全部分圏からの制限の充満忠実性と自明 Kan 性。
方針：指定 pinched 比較の同値に全部分圏の包含を合成し、厳密な頂点全射性を合わせる。
規約：相対 join の図式でなく元の C 上の関手全体を使う。
使われ方：一般の isofibration 上での左 Kan 拡張の coherent な選択の制限定理。

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

/-- 概要：元の相対左 Kan 関手の全部分圏からの相対制限は充満忠実。
方針：元の関手の始点境界充填による指定 pinched 比較と全部分圏の比較を合成する。
規約：局所相対余極限の存在は追加仮定にしない。
使われ方：一般の標的上の元の Kan 関手の写像空間の普遍性。 -/
lemma kanRelativeLeftKanRestriction_isFullyFaithful {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction U δ s) := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory U _ s
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  intro x y
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeLeftKanVertex U δ x.val at hx
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm x.val
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = x.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).apply_symm_apply _
  have hinit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting s.π x.val := by
    rw [← hF]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftFunctor_relative_initialBoundary δ hδ U hU s F hx
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams U δ).ι ≫ s.π) x y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _ x y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary _ x.val y.val hinit)

/-- 概要：標準局所相対余極限が存在すれば元の相対左 Kan 制限は自明 Kan。
方針：充満忠実性と inner 性に、元と底を厳密に保つ存在による頂点全射性を合わせる。
規約：δ は充満忠実な inner 単射、U は同値を持ち上げる。
使われ方：元の相対 Kan 関手の coherent な選択と制限の可縮な fiber。 -/
lemma kanRelativeLeftKanRestriction_trivialKanFibration {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U)
    (hlocal : ∀ (F₀ : K ⟶ D) (H₀ : C ⟶ E), F₀ ≫ U = δ ≫ H₀ →
      ∀ c : C _⦋0⦌, ∃ z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U z ∧ z.val ≫ U = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ H₀ c).val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction U δ s) := by
  have : InnerFibration U := hU.innerFibration
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_innerFibration U hU δ s
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory U _ s
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams U δ : SSet.{u}) :=
    inferInstanceAs (Quasicategory
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeLeftKanVertex U δ) : SSet.{u}))
  have hf := kanRelativeLeftKanRestriction_isFullyFaithful U hU δ hδ s
  exact hf.trivialKanFibration_of_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_surjective U hU δ hδ s hlocal)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.3.2.15" (partial := stronger-hyp) "仮定：充満部分圏の包含と圏ファイブレーション（Lean が強い：固定した底図式だけでなく、両立する任意の部分図式と底図式に対して局所相対余極限を要求）。結論：この仮定では標的の全関手が条件を満たす。相対左 Kan 関手の制限は自明 Kan ファイブレーションであり、固定底図式への引き戻しも自明 Kan となる（一致する場合）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_trivialKanFibration
attribute [cite HTT "4.3.2.16" (partial := stronger-hyp) "仮定：部分圏上の全関手に相対左 Kan 拡張が存在（Lean が強い：固定した底図式だけでなく、両立する任意の部分図式と底図式に対する局所相対余極限を要求）。結論：同じ相対制限の自明 Kan 性から切断を得る。切断の値は相対左 Kan 関手の充満部分圏にあり、同じ制限の繊維が可縮なのでその部分圏の全関手を本質像に含む（一致する場合）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction_trivialKanFibration
