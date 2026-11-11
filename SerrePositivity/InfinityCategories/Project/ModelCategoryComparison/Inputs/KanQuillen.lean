module

public import SerrePositivity.Spectra.ModelCategory.SimplicialWeakEquivalences
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-! # HT-KQ: the Kan–Quillen model existence input

Literature input: Mark Hovey, *Model Categories*, Mathematical Surveys and
Monographs 63, AMS (1999), Theorem 3.6.5, printed p. 98; generating maps in
§3.1 and geometric weak equivalences in §3.2 (with the topological definition
in Definition 2.4.3).
Source: https://ericmalm.net/ac/projects/symmetric-spectra/hovey--model-cats.pdf

Universe: the fixed `SSet.{u}`, with hom universe u. The weak class is the
inverse image under Mathlib's actual geometric realization of bijections on
path components and positive cubical homotopy classes at every source point.
These are the usual homotopy groups; bijectivity is their isomorphism criterion.
The component condition is imposed independently even for an empty source.
The boundary and horn classes are the actual fixed Mathlib I and J.

Only model existence with these three classes is cited. Cofibrant generation,
pointed transfer, monoidal/SM7 compatibility, free-level acyclicity, smallness,
and the circle-spectrum level model are proved in the independent modules.
No realization/singular Quillen equivalence or stable model is cited here.
This file is kept outside the proof-only foundations and their strict audit.
-/

@[expose] public section
universe u
open CategoryTheory HomotopicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs

/-- HT-KQ (Hovey, Theorem 3.6.5): existence for the explicitly defined three
classes. This is the sole unproved literature input in this module. -/
theorem kanQuillen_model_exists : ∃ m : ModelCategory SSet.{u},
    @cofibrations SSet.{u} _ m.categoryWithCofibrations =
      MorphismProperty.monomorphisms SSet.{u} ∧
    @fibrations SSet.{u} _ m.categoryWithFibrations = SSet.modelCategoryQuillen.J.{u}.rlp ∧
    @weakEquivalences SSet.{u} _ m.categoryWithWeakEquivalences =
      SimplicialModelInputs.geometricWeakEquivalences.{u} := by
  sorry

/-- A local choice of the cited model; this is deliberately not a global instance. -/
@[instance_reducible]
noncomputable def kanQuillenModel : ModelCategory SSet.{u} :=
  Classical.choose kanQuillen_model_exists

lemma kanQuillenModel_cofibrations :
    @cofibrations SSet.{u} _ kanQuillenModel.categoryWithCofibrations =
      MorphismProperty.monomorphisms SSet.{u} :=
  (Classical.choose_spec kanQuillen_model_exists).1

lemma kanQuillenModel_fibrations :
    @fibrations SSet.{u} _ kanQuillenModel.categoryWithFibrations =
      SSet.modelCategoryQuillen.J.{u}.rlp :=
  (Classical.choose_spec kanQuillen_model_exists).2.1

lemma kanQuillenModel_weakEquivalences :
    @weakEquivalences SSet.{u} _ kanQuillenModel.categoryWithWeakEquivalences =
      SimplicialModelInputs.geometricWeakEquivalences.{u} :=
  (Classical.choose_spec kanQuillen_model_exists).2.2

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs
