module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CellularNaturalComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinInitialComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinStdComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の二つの単体集合の fat join 比較の前合成による同値性。
方針：初期対象と標準単体の比較から、左右二回のセルによる還元を行う。
規約：両因子に quasicategory 性・有限性・非空性は要求しない。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV）、Example 4.6.6.8（Tag 04J5） の slice 比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：左因子が標準単体なら任意の右因子の fat join 比較は前合成の同値条件を満たす。
方針：右因子の標準単体での比較をセルの族と骨格の余極限で拡張する。
規約：右因子の有限性・非空性・quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の第一の変数の還元。 -/
lemma isPrecompositionEquivalence_fatJoinComparison_stdSimplex_left (n : ℕ) (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[n] : SSet.{u}) B) := by
  have : ∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinRightFunctor (Δ[n] : SSet.{u})) := fun _ ↦ inferInstance
  have : ∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightFunctor (Δ[n] : SSet.{u})) := fun _ ↦ inferInstance
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_natComponent_of_stdSimplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparisonRightNat (Δ[n] : SSet.{u})) ?_ ?_ B
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison_initial_right _ _ initialIsInitial
  · intro m
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison_stdSimplex n m

/-- 概要：任意の二つの単体集合の fat join 比較は全ての quasicategory への前合成で同値を誘導する。
方針：標準単体を左因子とした一般の比較を、左因子のセル分解で全単体集合へ拡張する。
規約：両因子は任意。比較自体の単射性や quasicategory 性は仮定しない。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の fat join と通常の join の比較。 -/
@[kerodon 01HV, kerodon 01HX, kerodon 01HY, kerodon 01HZ]
lemma isPrecompositionEquivalence_fatJoinComparison (A B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A B) := by
  have : ∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinLeftFunctor B) := fun _ ↦ inferInstance
  have : ∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftFunctor B) := fun _ ↦ inferInstance
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_natComponent_of_stdSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparisonLeftNat B) ?_ ?_ A
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison_initial_left (⊥_ SSet.{u}) initialIsInitial B
  · intro n
    exact isPrecompositionEquivalence_fatJoinComparison_stdSimplex_left n B

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.2.1.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison
