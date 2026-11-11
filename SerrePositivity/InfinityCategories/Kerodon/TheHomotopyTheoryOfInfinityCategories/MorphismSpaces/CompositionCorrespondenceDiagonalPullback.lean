module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonalSquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanEquivalenceLiftingFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
概要：合成三角形の同じ対角評価は、外ホーン制限の実際の pullback で Kan fibration。
方針：構成済みの同じ持ち上げと三角形の一意性で普遍性を示し、持ち上げ性を移す。
規約：標的の quasicategory 性だけを使い、追加のモデル圏仮定は要求しない。
使われ方：後合成 fiber と同じ指定外ホーン fiber の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)

/-- 同じ対角評価と三角形への射は、同じ外ホーン制限の実際の pullback。 -/
lemma compositionCorrespondenceDiagonal_isPullback :
    IsPullback (pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g)
      ((pre (horn 2 2).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cospanHomHornMap x g) := by
  refine IsPullback.mk' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonalSquare x g) ?_ ?_
  · intro T a b h₁ h₀
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_hom_ext_triangle x g a b h₁
  · intro T a b h
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonalLift x g a b h,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonalLift_triangle x g a b h,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonalLift_diagonalMap x g a b h⟩

/-- 同じ対角評価は、単射な前合成同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_compositionCorrespondenceDiagonal [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g) := by
  intro A B i hi he
  letI : HasLiftingProperty i ((pre (horn 2 2).ι).app X) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre (horn 2 2).ι i hi he
  exact (compositionCorrespondenceDiagonal_isPullback x g).hasLiftingProperty i

/-- 同じ対角評価は、Kan 複体間の元の射として Kan fibration。 -/
lemma compositionCorrespondenceDiagonal_fibration [Quasicategory X] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence_kanComplex x g
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_kanEquivalenceLifting_of_kanComplex _
    (kanEquivalenceLifting_compositionCorrespondenceDiagonal x g)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
