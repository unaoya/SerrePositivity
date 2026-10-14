module

public import SerrePositivity.HomotopicalAlgebra.Topological.WeakEquivalence
public import Mathlib.AlgebraicTopology.SingularSet

/-! # Geometric weak equivalences of the actual simplicial sets

The class is defined by the existing geometric realization functor and
its actual induced maps on components and homotopy classes. This definition
does not supply or assume the Kan–Quillen model existence theorem.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory
namespace SerrePositivity.SimplicialModelInputs

def geometricWeakEquivalences : MorphismProperty SSet.{u} :=
  TopologicalHomotopy.weakHomotopyEquivalences.inverseImage SSet.toTop

lemma geometricWeakEquivalences_id (X : SSet.{u}) : geometricWeakEquivalences (𝟙 X) := by
  change TopologicalHomotopy.weakHomotopyEquivalences (SSet.toTop.map (𝟙 X))
  rw [CategoryTheory.Functor.map_id]
  exact TopologicalHomotopy.weakHomotopyEquivalences_id _

lemma geometricWeakEquivalences_comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : geometricWeakEquivalences f) (hg : geometricWeakEquivalences g) :
    geometricWeakEquivalences (f ≫ g) := by
  change TopologicalHomotopy.weakHomotopyEquivalences (SSet.toTop.map (f ≫ g))
  rw [CategoryTheory.Functor.map_comp]
  exact TopologicalHomotopy.weakHomotopyEquivalences_comp hf hg

end SerrePositivity.SimplicialModelInputs
