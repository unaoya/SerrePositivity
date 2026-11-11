module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoreFlag.WeakEquivalence

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.RowComparison
public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialWeak

/-!
概要：一般 core 旗の対角評価の弱ホモトピー同値。
方針：転置した行の定数包含に行弱同値の対角定理を適用し、切断恒等式で消去する。
規約：頂点評価を旗次数について自然と扱わない。単体集合のモデル構造は使わない。
使われ方：Sp-8、K-cof に供給する一般 core 旗比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories
open EInfinity.Hammock.DoubleSimplicial

/-- 一般の quasicategory の定数 core 旗包含は弱ホモトピー同値。 -/
lemma inclusion_isWeakHomotopyEquivalence (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.inclusion C) := by
  have hconst := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalConstantIso C).symm).isWeakHomotopyEquivalence
  have hrow := diagonalFunctor_map_weak (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.bisimplicialInclusion C)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.rowInclusion_isWeakHomotopyEquivalence C)
  have htranspose := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoreFlag.diagonalTransposeIso C)).isWeakHomotopyEquivalence
  have h := hconst.comp (hrow.comp htranspose)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalConstantIso C).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.bisimplicialInclusion C) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoreFlag.diagonalTransposeIso C).hom) at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoreFlag.diagonal_bisimplicialInclusion] at h
  exact h

/-- 一般の quasicategory の core 旗の対角評価は弱ホモトピー同値。 -/
lemma counit_isWeakHomotopyEquivalence (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.counit C) := by
  apply (inclusion_isWeakHomotopyEquivalence C).cancel_left
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.inclusion_counit]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id C

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
