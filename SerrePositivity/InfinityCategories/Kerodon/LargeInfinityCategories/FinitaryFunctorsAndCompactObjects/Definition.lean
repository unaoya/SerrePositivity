module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CovariantRepresentableValues
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：κ-compact 対象を、元の全共変 Hom 関手による小さい κ-filtered 余極限保存で定義。
方針：添字の宇宙と標的の宇宙を分け、指定された全余錐の像をそのまま使う。
規約：通常の圏上の図式や Hom 集合への置き換えは行わない。HTT 5.3.4。
使われ方：Yoneda 像の compact 性、有限余極限・retract 閉性、Ind の compact 部分。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の全関手が、小さい κ-filtered 添字の指定された全余極限余錐を保存すること。 -/
def PreservesKappaFilteredColimits (κ : Cardinal.{u})
    {C : SSet.{max u v}} {Y : SSet.{max u v + 1}}
    (F : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶ Y) : Prop :=
  ∀ (I : SSet.{u}) [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c))

/-- 元の Map(x,−) が小さい κ-filtered 余極限を保つ、という κ-compact 性。 -/
@[kerodon 064F]
def IsKappaCompact (κ : Cardinal.{u}) {C : SSet.{max u v}} [Quasicategory C]
    (x : C _⦋0⦌) : Prop :=
  PreservesKappaFilteredColimits.{u, v} κ (C := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)

/-- compact は同じ全 Hom 関手についての ℵ₀-compact 性。 -/
@[kerodon 064A]
abbrev IsCompact {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) : Prop :=
  IsKappaCompact.{u, u} Cardinal.aleph0 x

/-- κ-filtered 保存は、より大きい濃度の filtered 保存を含む。 -/
lemma PreservesKappaFilteredColimits.of_le {κ μ : Cardinal.{u}} (hκμ : κ ≤ μ)
    {C : SSet.{max u v}} {Y : SSet.{max u v + 1}}
    {F : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶ Y}
    (h : PreservesKappaFilteredColimits.{u, v} κ F) :
    PreservesKappaFilteredColimits.{u, v} μ F := by
  intro I hI hFiltered D c hc
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_le hκμ
  exact h I D c hc

/-- κ-compact 対象は κ ≤ μ のとき μ-compact。 -/
lemma IsKappaCompact.of_le {κ μ : Cardinal.{u}} (hκμ : κ ≤ μ)
    {C : SSet.{max u v}} [Quasicategory C] {x : C _⦋0⦌}
    (h : IsKappaCompact.{u, v} κ x) : IsKappaCompact.{u, v} μ x :=
  PreservesKappaFilteredColimits.of_le hκμ h

/-- ℵ₀-compact 性は、一般の小さい filtered ∞ 圏上の元の余錐で判定する。 -/
@[kerodon 064A]
lemma isKappaCompact_aleph0_iff_filtered {C : SSet.{max u v}} [Quasicategory C] (x : C _⦋0⦌) :
    IsKappaCompact.{u, v} Cardinal.aleph0 x ↔
      ∀ (I : SSet.{u}) [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I]
        (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c)) := by
  constructor
  · intro h I hI hFiltered D c hc
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered Cardinal.aleph0 I := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_aleph0_iff I).mpr hFiltered
    exact h I D c hc
  · intro h I hI hFiltered D c hc
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_aleph0_iff I).mp hFiltered
    exact h I D c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
