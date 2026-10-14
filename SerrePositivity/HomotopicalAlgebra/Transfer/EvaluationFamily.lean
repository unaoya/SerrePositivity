module

public import SerrePositivity.HomotopicalAlgebra.Transfer.Recognition
public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

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

variable [ModelCategory C] [HasFiniteLimits D] [HasFiniteColimits D]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  [(generators L I).HasSmallObjectArgument.{w}]
  [(generators L J).HasSmallObjectArgument.{w}]

include adj in
/-- Transfer to the actual module category using all free/evaluation adjunctions. -/
@[instance_reducible]
def modelCategory
    (hacyclic : SerrePositivity.Quillen.relativeCells.{w} (generators L J) ≤
      detected R (weakEquivalences C)) : ModelCategory D := by
  letI := detectedFibrations R
  letI := detectedWeakEquivalences R
  letI := generatedCofibrations L I
  have : (weakEquivalences D).HasTwoOutOfThreeProperty :=
    inferInstanceAs ((detected R (weakEquivalences C)).HasTwoOutOfThreeProperty)
  have : (weakEquivalences D).IsStableUnderRetracts :=
    inferInstanceAs ((detected R (weakEquivalences C)).IsStableUnderRetracts)
  have hI : (generators L I).rlp = trivialFibrations D := by
    rw [generators_rlp L R adj, CofibrantlyGenerated.rlp_I (I := I) (J := J)]
    exact detected_inf R _ _
  have hJ : (generators L J).rlp = fibrations D := by
    rw [generators_rlp L R adj, CofibrantlyGenerated.rlp_J (I := I) (J := J)]
    rfl
  exact modelCategoryOfRecognition (generators L I) (generators L J) hI hJ rfl
    (generatedLeft_le_of_cells_le _ _ hacyclic)

lemma modelCategory_weakEquivalences (hacyclic) :
    @weakEquivalences D _ (modelCategory L R adj I J hacyclic).categoryWithWeakEquivalences =
      detected R (weakEquivalences C) := rfl

lemma modelCategory_fibrations (hacyclic) :
    @fibrations D _ (modelCategory L R adj I J hacyclic).categoryWithFibrations =
      detected R (fibrations C) := rfl

lemma modelCategory_generated (hacyclic) :
    let := modelCategory L R adj I J hacyclic
    CofibrantlyGenerated.{w} (generators L I) (generators L J) := by
  let := modelCategory L R adj I J hacyclic
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · rw [generators_rlp L R adj, CofibrantlyGenerated.rlp_I (I := I) (J := J)]
    exact detected_inf R _ _
  · rw [generators_rlp L R adj, CofibrantlyGenerated.rlp_J (I := I) (J := J)]
    rfl

lemma evaluation_isRightQuillen (hacyclic) (i : ι) :
    let := modelCategory L R adj I J hacyclic
    SerrePositivity.Quillen.IsRightQuillen (R i) := by
  let := modelCategory L R adj I J hacyclic
  exact ⟨fun _ _ _ hf ↦ hf i, fun _ _ _ hf ↦ ⟨hf.1 i, hf.2 i⟩⟩

lemma free_isLeftQuillen (hacyclic) (i : ι) :
    let := modelCategory L R adj I J hacyclic
    SerrePositivity.Quillen.IsLeftQuillen (L i) := by
  let := modelCategory L R adj I J hacyclic
  have := evaluation_isRightQuillen L R adj I J hacyclic i
  exact SerrePositivity.Quillen.isLeftQuillen_of_isRightQuillen (adj i)

lemma functorialFactorizations (hacyclic) :
    let := modelCategory L R adj I J hacyclic
    (cofibrations D).HasFunctorialFactorization (trivialFibrations D) ∧
      (trivialCofibrations D).HasFunctorialFactorization (fibrations D) := by
  let := modelCategory L R adj I J hacyclic
  have := modelCategory_generated L R adj I J hacyclic
  exact ⟨hasFunctorialFactorization_cofibration_trivialFibration
      (generators L I) (generators L J),
    hasFunctorialFactorization_trivialCofibration_fibration (generators L I) (generators L J)⟩

end SerrePositivity.ModelGeneration.EvaluationFamily
