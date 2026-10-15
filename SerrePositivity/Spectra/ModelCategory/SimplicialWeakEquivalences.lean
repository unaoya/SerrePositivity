module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.WeakEquivalence

/-! # Compatibility names for geometric simplicial weak equivalences

The proof-only definition now lives in the shared homotopical foundations.
The old Spectra names remain definitionally equal aliases.
-/

@[expose] public section
universe u
open CategoryTheory
namespace SerrePositivity.SimplicialModelInputs

abbrev geometricWeakEquivalences : MorphismProperty SSet.{u} :=
  SimplicialHomotopy.weakEquivalences

lemma geometricWeakEquivalences_id (X : SSet.{u}) : geometricWeakEquivalences (𝟙 X) :=
  SimplicialHomotopy.weakEquivalences_id X

lemma geometricWeakEquivalences_comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : geometricWeakEquivalences f) (hg : geometricWeakEquivalences g) :
    geometricWeakEquivalences (f ≫ g) :=
  SimplicialHomotopy.weakEquivalences_comp hf hg

end SerrePositivity.SimplicialModelInputs
