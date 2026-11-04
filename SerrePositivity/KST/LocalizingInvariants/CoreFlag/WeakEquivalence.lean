module
public import SerrePositivity.InfinityCategories.Stable.CoreFlag.WeakEquivalence

public import SerrePositivity.InfinityCategories.F1.CoreFlag.RowComparison
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
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories
open EInfinity.Hammock.DoubleSimplicial

/-- 一般の quasicategory の定数 core 旗包含は弱ホモトピー同値。 -/
lemma inclusion_isWeakHomotopyEquivalence (C : SSet.{u}) [Quasicategory C] :
    IsWeakHomotopyEquivalence (inclusion C) := by
  have hconst := (isPrecompositionEquivalence_of_iso
    (diagonalConstantIso C).symm).isWeakHomotopyEquivalence
  have hrow := diagonalFunctor_map_weak (bisimplicialInclusion C)
    (rowInclusion_isWeakHomotopyEquivalence C)
  have htranspose := (isPrecompositionEquivalence_of_iso
    (diagonalTransposeIso C)).isWeakHomotopyEquivalence
  have h := hconst.comp (hrow.comp htranspose)
  change IsWeakHomotopyEquivalence ((diagonalConstantIso C).inv ≫
    diagonalFunctor.map (bisimplicialInclusion C) ≫ (diagonalTransposeIso C).hom) at h
  rw [diagonal_bisimplicialInclusion] at h
  exact h

/-- 一般の quasicategory の core 旗の対角評価は弱ホモトピー同値。 -/
lemma counit_isWeakHomotopyEquivalence (C : SSet.{u}) [Quasicategory C] :
    IsWeakHomotopyEquivalence (counit C) := by
  apply (inclusion_isWeakHomotopyEquivalence C).cancel_left
  rw [inclusion_counit]
  exact isWeakHomotopyEquivalence_id C

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
