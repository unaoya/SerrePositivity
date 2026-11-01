module
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract


/-! # Right-induced models detected by a family of evaluations

The category D may be a category of enriched modules. It is not identified with
an ordinary functor category: free/evaluation adjunctions are input at each
object. Generator smallness and cell acyclicity are explicit transfer inputs.
-/

@[expose] public section
universe w t u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
namespace SerrePositivity.ModelGeneration.EvaluationFamily
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {ι : Type t} (L : ι → C ⥤ D) (R : ι → D ⥤ C) (adj : ∀ i, L i ⊣ R i)

/-- A property is detected at every evaluation. -/
def detected (P : MorphismProperty C) : MorphismProperty D :=
  fun _ _ f ↦ ∀ i, P ((R i).map f)

/-- All free-object images of the generating class. -/
def generators (P : MorphismProperty C) : MorphismProperty D := ⨆ i, P.strictMap (L i)

lemma detected_inf (P Q : MorphismProperty C) :
    detected R (P ⊓ Q) = detected R P ⊓ detected R Q := by
  ext A B f
  constructor
  · intro h
    exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩
  · rintro ⟨hp, hq⟩ i
    exact ⟨hp i, hq i⟩

include adj in
lemma generators_rlp (P : MorphismProperty C) :
    (generators L P).rlp = detected R P.rlp := by
  ext A B f
  constructor
  · intro h i X Y g hg
    exact ((adj i).hasLiftingProperty_iff g f).1
      (h _ ((le_iSup (fun i ↦ P.strictMap (L i)) i) _ (P.map_mem_strictMap _ g hg)))
  · intro h X Y g hg
    change (⨆ i, P.strictMap (L i)) g at hg
    rw [MorphismProperty.iSup_iff] at hg
    obtain ⟨i, hg⟩ := hg
    cases hg with
    | map hg => exact ((adj i).hasLiftingProperty_iff _ f).2 (h i _ hg)

instance detected_twoOutOfThree (P : MorphismProperty C) [P.HasTwoOutOfThreeProperty] :
    (detected R P).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg i := by
    rw [(R i).map_comp]
    exact P.comp_mem _ _ (hf i) (hg i)
  of_postcomp f g hg hfg i := by
    apply P.of_postcomp ((R i).map f) ((R i).map g) (hg i)
    simpa only [(R i).map_comp] using hfg i
  of_precomp f g hf hfg i := by
    apply P.of_precomp ((R i).map f) ((R i).map g) (hf i)
    simpa only [(R i).map_comp] using hfg i

instance detected_retracts (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    (detected R P).IsStableUnderRetracts where
  of_retract h hg i := MorphismProperty.of_retract (h.map (R i)) (hg i)

@[instance_reducible]
def detectedFibrations [CategoryWithFibrations C] : CategoryWithFibrations D where
  fibrations := detected R (fibrations C)

@[instance_reducible]
def detectedWeakEquivalences [CategoryWithWeakEquivalences C] :
    CategoryWithWeakEquivalences D where
  weakEquivalences := detected R (weakEquivalences C)

@[instance_reducible]
def generatedCofibrations (I : MorphismProperty C) : CategoryWithCofibrations D where
  cofibrations := (generators L I).rlp.llp

end SerrePositivity.ModelGeneration.EvaluationFamily
