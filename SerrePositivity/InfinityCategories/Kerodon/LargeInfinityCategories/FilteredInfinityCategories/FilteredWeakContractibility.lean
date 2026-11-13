module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.HTT.Section2_1_3.WeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.ContinuousKanCoconeContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ContinuousKanFiniteFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredCoslices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiniteSubcomplexes
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：一般の filtered ∞ 圏と有限図式の下の coslice は弱可縮。
方針：連続 Kan 置換への境界を有限部分に下ろし、有限余錐の収縮で充填する。
規約：元の ∞ 圏に Kan 性や追加の余極限存在を仮定しない。
使われ方：Kerodon 9.1.1.17（Tag 02PH）、filtered 添字の cofinality。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：filtered ∞ 圏の具体的な連続 Kan 置換は全境界を充填する。
方針：有限部分の包含の収縮を写像空間の成分で移し、境界の同型で充填を戻す。
規約：零次元の空境界も含む。
使われ方：filtered ∞ 圏の弱可縮性の Kan 模型での証明。 -/
lemma continuousKanReplacement_isContractibleKan_of_filtered (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj C) := by
  intro n b
  obtain ⟨A, g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_boundary_factorization C n b
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity.cocone_nonempty A.val.ι
  obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_map_null_of_cocone A.val.ι c
  have h := congrArg (SSet.mapπ₀ ((pre g).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj C))) hx
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map A.val.ι)) =
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ SSet.const x)) at h
  rw [hg, SSet.comp_const] at h
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.nonempty_vertexIso_of_piZero_eq h.symm
  exact (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.const x) b from e).exists_boundaryFilling
    ⟨SSet.const x, by rw [SSet.comp_const]⟩

/-- 概要：全ての filtered ∞ 圏は弱可縮。
方針：証明した Kan 置換の可縮性を元の単位の弱同値で反映する。
規約：C の Kan 性を仮定しない。使われ方：Kerodon 9.1.1.17（Tag 02PH） と Quillen A。 -/
@[kerodon 02PH]
lemma isWeaklyContractible_of_isFilteredInfinity (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence C).weaklyContractible_iff.2
    (continuousKanReplacement_isContractibleKan_of_filtered C).isWeaklyContractible

/-- 概要：filtered ∞ 圏の有限図式の下の coslice は弱可縮。
方針：有限図式の coslice の filtered 性と一般の弱可縮性を合成する。
規約：元の有限図式 p 全体を固定する。使われ方：filtered 性の cofinality 判定。 -/
lemma isWeaklyContractible_sliceUnder_of_filtered {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] (p : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :=
  isWeaklyContractible_of_isFilteredInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.3.1.20"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity
