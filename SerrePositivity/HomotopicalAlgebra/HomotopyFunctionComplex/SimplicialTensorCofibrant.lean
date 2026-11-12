module
public import SerrePositivity.HomotopicalAlgebra.Enriched.TensorCotensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FiniteTensorAdjunction
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.StandardCosimplicial
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.FiniteTensorAdjunction


/-! # Reedy cofibrancy of the actual simplicial tensor family

The boundary condition is derived from tensor representability and the
Quillen bifunctor property. It is not an extra frame hypothesis.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.Quillen

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  [EnrichedOrdinaryCategory SSet.{v} C]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C) [IsQuillenBifunctor S.tensor]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma tensorCosimplicial_reedyCofibrant (X : C) [IsCofibrant X] :
    reedyLeft simplex (cofibrations C)
      (Limits.initial.to ((tensorCosimplicialFamily S).obj X)) := by
  have : (S.tensor.flip.obj X).IsLeftAdjoint := (S.tensorHom.adj X).isLeftAdjoint
  have : IsLeftQuillen (S.tensor.flip.obj X) :=
    SerrePositivity.Enriched.tensor_parameter_isLeftQuillen S X
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.reedy_cofibrant (S.tensor.flip.obj X) hcof

end SerrePositivity.HomotopyFunctionComplex
