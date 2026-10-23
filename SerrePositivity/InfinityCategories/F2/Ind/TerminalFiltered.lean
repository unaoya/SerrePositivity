module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredInfinity
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-!
概要：終対象を持つ元の ∞ 圏は、任意の κ で κ-filtered。
方針：終対象上の slice 射影の切断を取り、任意の図式を同じ終対象への余錐へ延長する。
規約：κ-filtered 性の定義は F2N-1 を再利用する。κ の正則性は不要。
使われ方：表現可能前層の元の圏の κ-filtered 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 終対象への slice の切断は、元の任意の図式を同じ終対象への余錐へ延長する。 -/
lemma nonempty_joinCocone_of_isTerminalVertex {K X : SSet.{u}}
    {x : X _⦋0⦌} (hx : IsTerminalVertex x) (f : K ⟶ X) : Nonempty (JoinCocone f) := by
  have := (isTerminalVertex_iff_trivialKanFibration x).mp hx
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section
    (sliceOverProjection (SSet.yonedaEquiv.symm x))
  refine ⟨⟨sliceOverUncurry (f ≫ s), ?_⟩⟩
  rw [sliceOverUncurry_projection, Category.assoc, hs, Category.comp_id]

/-- 終対象を持つ元の ∞ 圏は、同じ任意の κ に対して κ-filtered。 -/
lemma isKappaFiltered_of_isTerminalVertex (κ : Cardinal.{u}) {X : SSet.{u}}
    [Quasicategory X] {x : X _⦋0⦌} (hx : IsTerminalVertex x) : IsKappaFiltered κ X where
  cocone_nonempty _ f := nonempty_joinCocone_of_isTerminalVertex hx f

end SerrePositivity.InfinityCategories.F2.Ind
