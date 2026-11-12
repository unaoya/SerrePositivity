module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.SetTheory.Cardinal.Regular

/-!
分割で生成：docstring を書き直すこと
 # Concrete smallness of the fixed simplicial generating maps

The boundary and horn domains have the same aleph-zero presentability bound
in the SSet hom-universe. These statements do not assume a completed
Kan-Quillen model structure, nor introduce a weak-equivalence class.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
open SSet SSet.modelCategoryQuillen
attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] Cardinal.orderBotAleph0OrdToType
/-- Every simplicial set is cofibrant for the fixed monomorphism cofibration class. -/
lemma simplicialSet_isCofibrant (X : SSet.{u}) : IsCofibrant X := by
  exact SSet.modelCategoryQuillen.cofibration_of_mono (initial.to X)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
