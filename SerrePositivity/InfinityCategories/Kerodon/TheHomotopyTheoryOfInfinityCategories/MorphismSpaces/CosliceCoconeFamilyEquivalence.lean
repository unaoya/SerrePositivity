module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensorRight
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceLaxEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FatJoinRightTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FatJoinRightTensorComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.LaxCoslice
public import Mathlib.Tactic.CrossRefAttribute

/-! # Coslice と固定図式上の余錐の族の同値

概要：直接定義した coslice と、固定図式上の余錐の関手圏は同値である。
方針：太い coslice への二つの比較を同定し、同値の二対三則を使う。
規約：図式を高次単体でも厳密に固定する。使われ方：余極限性と族の普遍性の接続。

対応節は Kerodon 4.6（Tag 01J3）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：coslice から余錐の族を経た太い coslice への比較は、直接の比較に一致する。
方針：fiber の包含後に uncurry し、二つの右直積比較の整合性を使う。
規約：quasicategory 性は不要。使われ方：比較同値の二対三則。 -/
lemma cosliceCoconeFamilyMap_comp_coconeFamilyLaxCosliceMap {K X : SSet.{u}} (p : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyMap p ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeFamilyLaxCosliceMap p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceLaxMap p := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (Δ[0] : SSet.{u}))).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
  change curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyUncurry p) ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K (Δ[0] : SSet.{u}))).app X =
    curry (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K S ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (𝟙 S)))
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyUncurry, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceCurryFamily]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K (Δ[0] : SSet.{u}) ▷ S),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableFatJoinTensorRight_comparison]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K ((Δ[0] : SSet.{u}) ⊗ S)),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison_naturality]
  rfl

/-- 概要：coslice と固定図式上の余錐の族の比較は quasicategory の同値。
方針：太い coslice への二つの比較の同値性と合成の同定を使う。
規約：値域は quasicategory、図式の形状は任意。使われ方：余極限の族の比較。 -/
@[kerodon 04J5]
lemma isQCatEquivalence_cosliceCoconeFamilyMap {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyMap p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isQCatEquivalence_coconeFamilyLaxCosliceMap p).cancel_right
  rw [cosliceCoconeFamilyMap_comp_coconeFamilyLaxCosliceMap]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceLaxMap p

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
