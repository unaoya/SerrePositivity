module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteUniverse
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallSimplicialSet
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EquivalenceDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRestriction

/-!
概要：小さい filtered ∞ 圏の任意の宇宙持ち上げも、一般の有限試験形状について filtered。
方針：有限形状を次数ごとに縮小し、元の余錐を持ち上げて元の全試験図式へ戻す。
規約：通常の図式に制限せず、任意の有限単体集合を試験する。
使われ方：大きい標的の compact 性と、一般 coherent 有限極限・filtered 余極限交換。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 有限な元の大きい形状を、小さい宇宙の同じ有限形状へ縮小する。 -/
lemma finite_smallSimplicialSet (K : SSet.{max u v}) [K.Finite]
    [∀ n, Small.{u} (K.obj n)] : SSet.Finite (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, v} K) := by
  have := SSet.finite_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, v} K).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.finite_ulift_iff.{u, v} _).mp this

/-- 元の filtered ∞ 圏を持ち上げても、元の一般有限試験図式に余錐が存在する。 -/
lemma isFilteredInfinity_ulift (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity ((SSet.uliftFunctor.{v, u}).obj C) := by
  constructor
  intro K hK f
  have (n : SimplexCategoryᵒᵖ) : Small.{u} (K.obj n) := inferInstance
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, v} K
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, v} K
  have : A.Finite := finite_smallSimplicialSet K
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (e.hom ≫ f)
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity.cocone_nonempty g
  have hg : (SSet.uliftFunctor.{v, u}).map g = e.hom ≫ f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _
  have h : e.inv ≫ (SSet.uliftFunctor.{v, u}).map g = f := by
    rw [hg, Iso.inv_hom_id_assoc]
  exact ⟨h ▸ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u, v} c).restrict e.inv⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
