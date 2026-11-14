module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Universe lift of actual simplicial generating maps

The standard simplex, boundary and horn in the larger universe are
explicitly isomorphic to the universe lifts of the smaller objects.
Both sides of each generating inclusion are compared as actual arrows.
-/

@[expose] public section
universe w v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

instance full : SSet.uliftFunctor.{w, v}.Full := by
  unfold SSet.uliftFunctor
  infer_instance

instance faithful : SSet.uliftFunctor.{w, v}.Faithful := by
  unfold SSet.uliftFunctor
  infer_instance

instance preservesColimits : PreservesColimitsOfSize.{v, v} SSet.uliftFunctor.{w, v} := by
  apply preservesColimits_of_evaluation
  intro n
  change PreservesColimitsOfSize.{v, v}
    ((evaluation SimplexCategoryᵒᵖ (Type v)).obj n ⋙ CategoryTheory.uliftFunctor.{w, v})
  infer_instance

instance preservesPushouts : PreservesColimitsOfShape WalkingSpan SSet.uliftFunctor.{w, v} := by
  apply preservesColimitsOfShape_of_evaluation
  intro n
  change PreservesColimitsOfShape WalkingSpan
    ((evaluation SimplexCategoryᵒᵖ (Type v)).obj n ⋙ CategoryTheory.uliftFunctor.{w, v})
  infer_instance

def simplexIso (n : SimplexCategory) :
    SSet.uliftFunctor.{w, v}.obj (SSet.stdSimplex.{v}.obj n) ≅
      SSet.stdSimplex.{max v w}.obj n :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun s => ⟨s.down.down⟩
      invFun := fun s => ⟨⟨s.down⟩⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }) (by intro m n f; ext s; rfl)

def boundaryIso (n : ℕ) :
    SSet.uliftFunctor.{w, v}.obj (SSet.boundary.{v} n).toSSet ≅
      (SSet.boundary.{max v w} n).toSSet :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun s => ⟨⟨s.down.val.down⟩, s.down.property⟩
      invFun := fun s => ⟨⟨⟨s.val.down⟩, s.property⟩⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }) (by intro m n f; ext s; rfl)

def hornIso (n : ℕ) (i : Fin (n + 1)) :
    SSet.uliftFunctor.{w, v}.obj (SSet.horn.{v} n i).toSSet ≅
      (SSet.horn.{max v w} n i).toSSet :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun s => ⟨⟨s.down.val.down⟩, s.down.property⟩
      invFun := fun s => ⟨⟨⟨s.val.down⟩, s.property⟩⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }) (by intro m n f; ext s; rfl)

def boundaryArrowIso (n : ℕ) :
    Arrow.mk (SSet.uliftFunctor.{w, v}.map (SSet.boundary.{v} n).ι) ≅
      Arrow.mk (SSet.boundary.{max v w} n).ι :=
  Arrow.isoMk (boundaryIso n) (simplexIso (SimplexCategory.mk n)) (by ext m s; rfl)

def hornArrowIso (n : ℕ) (i : Fin (n + 1)) :
    Arrow.mk (SSet.uliftFunctor.{w, v}.map (SSet.horn.{v} n i).ι) ≅
      Arrow.mk (SSet.horn.{max v w} n i).ι :=
  Arrow.isoMk (hornIso n i) (simplexIso (SimplexCategory.mk n)) (by ext m s; rfl)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
