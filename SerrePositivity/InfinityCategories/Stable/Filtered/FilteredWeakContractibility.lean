module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.ContractibleKan
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakContractibility
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.ContinuousKanCoconeContraction
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ContinuousKanFiniteFactorization
public import SerrePositivity.InfinityCategories.Stable.Filtered.FilteredCoslices
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FiniteSubcomplexes

/-!
概要：一般の filtered ∞ 圏と有限図式の下の coslice は弱可縮。
方針：連続 Kan 置換への境界を有限部分に下ろし、有限余錐の収縮で充填する。
規約：元の ∞ 圏に Kan 性や追加の余極限存在を仮定しない。
使われ方：Kerodon 9.1.1.17、filtered 添字の cofinality。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：filtered ∞ 圏の具体的な連続 Kan 置換は全境界を充填する。
方針：有限部分の包含の収縮を写像空間の成分で移し、境界の同型で充填を戻す。
規約：零次元の空境界も含む。
使われ方：filtered ∞ 圏の弱可縮性の Kan 模型での証明。 -/
lemma continuousKanReplacement_isContractibleKan_of_filtered (C : SSet.{u})
    [Quasicategory C] [IsFilteredInfinity C] :
    IsContractibleKan (continuousKanReplacement.obj C) := by
  intro n b
  obtain ⟨A, g, hg⟩ := continuousKanReplacement_boundary_factorization C n b
  obtain ⟨c⟩ := IsFilteredInfinity.cocone_nonempty A.val.ι
  obtain ⟨x, hx⟩ := continuousKanReplacement_map_null_of_cocone A.val.ι c
  have h := congrArg (SSet.mapπ₀ ((pre g).app (continuousKanReplacement.obj C))) hx
  change SSet.π₀.mk (functorVertex (g ≫ continuousKanReplacement.map A.val.ι)) =
    SSet.π₀.mk (functorVertex (g ≫ SSet.const x)) at h
  rw [hg, SSet.comp_const] at h
  obtain ⟨e⟩ := nonempty_vertexIso_of_piZero_eq h.symm
  exact (show FunctorIso (SSet.const x) b from e).exists_boundaryFilling
    ⟨SSet.const x, by rw [SSet.comp_const]⟩

/-- 概要：全ての filtered ∞ 圏は弱可縮。
方針：証明した Kan 置換の可縮性を元の単位の弱同値で反映する。
規約：C の Kan 性を仮定しない。使われ方：Kerodon 9.1.1.17 と Quillen A。 -/
lemma isWeaklyContractible_of_isFilteredInfinity (C : SSet.{u}) [Quasicategory C]
    [IsFilteredInfinity C] : IsWeaklyContractible C :=
  (continuousKanReplacementUnit_isWeakHomotopyEquivalence C).weaklyContractible_iff.2
    (continuousKanReplacement_isContractibleKan_of_filtered C).isWeaklyContractible

/-- 概要：filtered ∞ 圏の有限図式の下の coslice は弱可縮。
方針：有限図式の coslice の filtered 性と一般の弱可縮性を合成する。
規約：元の有限図式 p 全体を固定する。使われ方：filtered 性の cofinality 判定。 -/
lemma isWeaklyContractible_sliceUnder_of_filtered {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] [IsFilteredInfinity C] (p : K ⟶ C) :
    IsWeaklyContractible (sliceUnder p) :=
  isWeaklyContractible_of_isFilteredInfinity (sliceUnder p)

end SerrePositivity.InfinityCategories.F2
