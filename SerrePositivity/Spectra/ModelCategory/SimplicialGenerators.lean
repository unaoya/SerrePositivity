module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness

/-! # Concrete smallness of the fixed simplicial generating maps

The boundary and horn domains have the same aleph-zero presentability bound
in the SSet hom-universe. These statements do not assume a completed
Kan-Quillen model structure, nor introduce a weak-equivalence class.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
namespace SerrePositivity.SimplicialModelInputs
open SSet SSet.modelCategoryQuillen
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

lemma boundaryGenerator_domain_presentable {A B : SSet.{u}} (f : A ⟶ B) (hf : I f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := by
  rcases hf with ⟨n⟩
  infer_instance

lemma hornGenerator_domain_presentable {A B : SSet.{u}} (f : A ⟶ B) (hf : J f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := by
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  infer_instance

lemma boundaryGenerators_isSmall : I.{u}.IsSmall.{u} := by
  exact MorphismProperty.isSmall_ofHoms _

lemma boundaryGenerators_cardinal :
    MorphismProperty.IsCardinalForSmallObjectArgument I.{u} Cardinal.aleph0.{u} := by
  let : I.{u}.IsSmall.{u} := boundaryGenerators_isSmall
  refine { preservesColimit := ?_ }
  intro A B X Y f hf g hg
  have : IsCardinalPresentable A Cardinal.aleph0.{u} := boundaryGenerator_domain_presentable f hf
  infer_instance

/-- The source boundary generators themselves have the small-object argument. -/
lemma boundaryGenerators_smallObjectArgument : I.{u}.HasSmallObjectArgument.{u} := by
  let : MorphismProperty.IsCardinalForSmallObjectArgument I.{u} Cardinal.aleph0.{u} :=
    boundaryGenerators_cardinal
  exact ⟨Cardinal.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The source horn small-object argument is reused from the fixed Mathlib. -/
lemma hornGenerators_smallObjectArgument : J.{u}.HasSmallObjectArgument.{u} := inferInstance

/-- Every simplicial set is cofibrant for the fixed monomorphism cofibration class. -/
lemma simplicialSet_isCofibrant (X : SSet.{u}) : IsCofibrant X := by
  exact SSet.modelCategoryQuillen.cofibration_of_mono (initial.to X)

end SerrePositivity.SimplicialModelInputs
