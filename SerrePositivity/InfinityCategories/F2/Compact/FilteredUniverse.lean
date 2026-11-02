module

public import SerrePositivity.InfinityCategories.F2.Compact.FiniteUniverse
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.F1.Universe.SmallSimplicialSet
public import SerrePositivity.InfinityCategories.F1.Universe.EquivalenceDescent
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.Stable.ColimitRestriction

/-!
概要：小さい filtered ∞ 圏の任意の宇宙持ち上げも、一般の有限試験形状について filtered。
方針：有限形状を次数ごとに縮小し、元の余錐を持ち上げて元の全試験図式へ戻す。
規約：通常の図式に制限せず、任意の有限単体集合を試験する。
使われ方：大きい標的の compact 性と、一般 coherent 有限極限・filtered 余極限交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 有限な元の大きい形状を、小さい宇宙の同じ有限形状へ縮小する。 -/
lemma finite_smallSimplicialSet (K : SSet.{max u v}) [K.Finite]
    [∀ n, Small.{u} (K.obj n)] : SSet.Finite (smallSimplicialSet.{u, v} K) := by
  have := SSet.finite_of_iso (smallSimplicialSetIso.{u, v} K).symm
  exact (finite_ulift_iff.{u, v} _).mp this

/-- 元の filtered ∞ 圏を持ち上げても、元の一般有限試験図式に余錐が存在する。 -/
lemma isFilteredInfinity_ulift (C : SSet.{u}) [Quasicategory C] [IsFilteredInfinity C] :
    IsFilteredInfinity ((SSet.uliftFunctor.{v, u}).obj C) := by
  constructor
  intro K hK f
  have (n : SimplexCategoryᵒᵖ) : Small.{u} (K.obj n) := inferInstance
  let A := smallSimplicialSet.{u, v} K
  let e := smallSimplicialSetIso.{u, v} K
  have : A.Finite := finite_smallSimplicialSet K
  let g := uliftMorphismDown (e.hom ≫ f)
  obtain ⟨c⟩ := IsFilteredInfinity.cocone_nonempty g
  have hg : (SSet.uliftFunctor.{v, u}).map g = e.hom ≫ f := uliftMorphismDown_lift _
  have h : e.inv ≫ (SSet.uliftFunctor.{v, u}).map g = f := by
    rw [hg, Iso.inv_hom_id_assoc]
  exact ⟨h ▸ (JoinCocone.ulift.{u, v} c).restrict e.inv⟩

end SerrePositivity.InfinityCategories.F2.Compact
