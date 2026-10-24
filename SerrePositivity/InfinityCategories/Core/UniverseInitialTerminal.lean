module
public import SerrePositivity.InfinityCategories.Core.UniverseBoundaryFilling
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-! General declarations moved verbatim from their original modules. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 実終対象性は宇宙持ち上げで保ち反映される。 -/
lemma isTerminalVertex_iff_ulift {X : SSet.{u}} (x : X _⦋0⦌) :
    IsTerminalVertex x ↔
      IsTerminalVertex (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) :=
  uliftBoundary_filling_at_vertex_iff x (fun n => Fin.last (n + 1))


/-- 実始対象性は宇宙持ち上げで保ち反映される。 -/
lemma isInitialVertex_iff_ulift {X : SSet.{u}} (x : X _⦋0⦌) :
    IsInitialVertex x ↔
      IsInitialVertex (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) :=
  uliftBoundary_filling_at_vertex_iff x (fun _ => 0)


end SerrePositivity.InfinityCategories
