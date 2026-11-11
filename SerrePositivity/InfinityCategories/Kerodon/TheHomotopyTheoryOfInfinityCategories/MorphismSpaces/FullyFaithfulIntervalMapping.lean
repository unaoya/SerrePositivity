module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostHomCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ParametrizedPointTransportSquare
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：充満忠実な元の射は、区間模型の実際の Hom 作用にも同値を誘導する。
方針：標準 pinched Hom との自然性を使い、両側の模型比較の同値を消去する。
規約：元の射の intervalMappingPost そのものについて述べる。
使われ方：局所化による図式制限の充満忠実性を、c1 の全変換空間の制限へ渡す。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 充満忠実な射の実際の区間 Hom への作用は、全対象対で同値。 -/
@[kerodon 06QP]
lemma IsFullyFaithful.intervalMappingPost_isQCatEquivalence
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost f x y) := by
  have h := (hf x y).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence (f.app _ x) (f.app _ y))
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq f x y rfl rfl
  simp only [eqToHom_refl, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalMappingPostOfEq_refl] at hc
  rw [hc] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).cancel_left h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsFullyFaithful (intervalMappingPost_isQCatEquivalence)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
