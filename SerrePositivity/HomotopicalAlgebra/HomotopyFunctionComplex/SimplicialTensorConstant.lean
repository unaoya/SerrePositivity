module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorCofibrant
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-! # Homotopical constancy of the actual standard tensor diagram

The geometric weak equivalences of standard simplices are proved by based
contractions. Brown preservation by the tensor left Quillen functor then
proves homotopical constancy; it is not assumed as a frame hypothesis.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.Quillen

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{v} = SimplicialHomotopy.weakEquivalences)

include hcof in
lemma simplicial_isCofibrant_of_mono (K : SSet.{v}) : IsCofibrant K := by
  constructor
  rw [hcof]
  change Mono (Limits.initial.to K)
  infer_instance

include hcof hw in
lemma standardCosimplicial_homotopicallyConstant (F : SSet.{v} ⥤ C) [IsLeftQuillen F]
    {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((SSet.stdSimplex ⋙ F).map f) := by
  have := simplicial_isCofibrant_of_mono hcof (SSet.stdSimplex.{v}.obj n)
  have := simplicial_isCofibrant_of_mono hcof (SSet.stdSimplex.{v}.obj m)
  have : WeakEquivalence (SSet.stdSimplex.{v}.map f) :=
    (weakEquivalence_iff _).mpr (hw.symm ▸ SimplicialHomotopy.stdSimplex_map_weakEquivalence f)
  exact (weakEquivalence_iff _).mp (map_weakEquivalence_of_cofibrant F (SSet.stdSimplex.map f))

variable [EnrichedOrdinaryCategory SSet.{v} C]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C) [IsQuillenBifunctor S.tensor]

include hcof hw in
lemma tensorCosimplicial_homotopicallyConstant (X : C) [IsCofibrant X]
    {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C (((tensorCosimplicialFamily S).obj X).map f) := by
  have : IsLeftQuillen (S.tensor.flip.obj X) :=
    SerrePositivity.Enriched.tensor_parameter_isLeftQuillen S X
  exact standardCosimplicial_homotopicallyConstant hcof hw (S.tensor.flip.obj X) f

end SerrePositivity.HomotopyFunctionComplex
