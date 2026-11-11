module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.EvaluationFamily

public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-! # The projective model structure on small diagrams

The original combinatorial model supplies the two generating classes.
Free/evaluation adjunctions, generator smallness and cell acyclicity are
proved for the actual ordinary functor category. No diagram-model existence
axiom or extra tensor compatibility is assumed.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.Projective
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

abbrev free (k : K) : C ⥤ K ⥤ C := evaluationLeftAdjoint C k
abbrev evaluation (k : K) : (K ⥤ C) ⥤ C := (CategoryTheory.evaluation K C).obj k
abbrev adjunction (k : K) : free K (C := C) k ⊣ evaluation K (C := C) k :=
  evaluationAdjunctionRight C k
abbrev generators (P : MorphismProperty C) :=
  ModelGeneration.EvaluationFamily.generators (free K) P
abbrev objectwise (P : MorphismProperty C) :=
  ModelGeneration.EvaluationFamily.detected (evaluation K) P

lemma free_map_trivialCofibration (k l : K) {X Y : C} (f : X ⟶ Y)
    [Cofibration f] [WeakEquivalence f] :
    trivialCofibrations C (((free K k).map f).app l) := by
  exact mem_trivialCofibrations (Limits.Sigma.map (fun _ : k ⟶ l ↦ f))

omit [IsLocallyPresentable.{w} C] in
lemma trivialCofibration_cells :
    Quillen.relativeCells.{w} (trivialCofibrations C) ≤ trivialCofibrations C := by
  rw [← fibrations_llp]
  exact (MorphismProperty.transfiniteCompositions_monotone
    ((MorphismProperty.pushouts_monotone (fibrations C).llp.coproducts_le).trans
      (fibrations C).llp.pushouts_le)).trans (fibrations C).llp.transfiniteCompositions_le

variable (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

include I in
lemma freeGenerators_trivialCofibrations (l : K) :
    generators K J ≤ (trivialCofibrations C).inverseImage (evaluation K l) := by
  intro A B f hf
  change (⨆ k, J.strictMap (free K k)) f at hf
  rw [MorphismProperty.iSup_iff] at hf
  obtain ⟨k, hf⟩ := hf
  cases hf with
  | @map X Y f hf =>
    have ht : trivialCofibrations C f :=
      (J.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J).symm.le) _ hf
    have : Cofibration f := ⟨ht.1⟩
    have : WeakEquivalence f := ⟨ht.2⟩
    exact free_map_trivialCofibration K k l f

include I in
lemma freeCells_acyclic : Quillen.relativeCells.{w} (generators K J) ≤
    objectwise K (weakEquivalences C) := by
  intro A B f hf l
  have : PreservesColimitsOfSize.{w, w} (evaluation K (C := C) l) :=
    { preservesColimitsOfShape := by intros; infer_instance }
  have h := ModelGeneration.relativeCells_map_le (evaluation K l) _ (trivialCofibrations C)
    (freeGenerators_trivialCofibrations K I J l) f hf
  exact (trivialCofibration_cells ((evaluation K l).map f) h).2

lemma generators_smallObjectArgument (P : MorphismProperty C) [P.HasSmallObjectArgument.{w}] :
    (generators K P).HasSmallObjectArgument.{w} := by
  have : P.IsSmall.{w} := ModelGeneration.EvaluationFamily.isSmall_of_smallObjectArgument P
  have : (generators K P).IsSmall.{w} :=
    ModelGeneration.EvaluationFamily.generators_isSmall (free K) P
  have := Smith.AccessibleLimits.functorCategory_isLocallyPresentable.{w} (C := C) K
  exact Smith.hasSmallObjectArgument (generators K P)

/-- The actual projective model, without acyclicity or smallness inputs. -/
@[instance_reducible]
def modelCategory : ModelCategory (K ⥤ C) := by
  have := generators_smallObjectArgument K I
  have := generators_smallObjectArgument K J
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCategory (free K) (evaluation K) (adjunction K) I J
    (freeCells_acyclic K I J)

lemma modelCategory_weakEquivalences :
    @weakEquivalences (K ⥤ C) _ (modelCategory K I J).categoryWithWeakEquivalences =
      objectwise K (weakEquivalences C) := rfl

lemma modelCategory_fibrations :
    @fibrations (K ⥤ C) _ (modelCategory K I J).categoryWithFibrations =
      objectwise K (fibrations C) := rfl

lemma modelCategory_generated :
    let := modelCategory K I J
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (generators K I) (generators K J) := by
  have := generators_smallObjectArgument K I
  have := generators_smallObjectArgument K J
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCategory_generated
    (free K) (evaluation K) (adjunction K) I J (freeCells_acyclic K I J)

end SerrePositivity.DiagramModel.Projective
