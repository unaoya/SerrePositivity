module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.EvaluationFamily

public import SerrePositivity.HomotopicalAlgebra.Simplicial.EvaluationMorphismProperties

/-! # Monoid-axiom acyclicity for many-object module transfer

Evaluation of a free generator may tensor it with an arbitrary Hom object.
Colimit-preserving evaluations and the monoid axiom control all free J-cells;
cofibrancy of these Hom objects is not imposed. The actual enriched module
category and its free/evaluation functors are supplied by the concrete theory.
-/

@[expose] public section
universe w t u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.ModelGeneration
namespace SerrePositivity.ManyObjectModelTransfer
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {ι : Type t} (L : ι → C ⥤ D) (R : ι → D ⥤ C)
  [MonoidalCategory C] [ModelCategory C] [HasMonoidAxiom.{w} C]
  [∀ i, PreservesColimitsOfSize.{w, w} (R i)]
  [∀ i, PreservesColimitsOfShape WalkingSpan (R i)]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

include I in
/-- Free J-cells are detected as weak equivalences at every module object. -/
lemma freeCells_acyclic
    (hfree : ∀ i j, J.strictMap (L i) ≤ (tensorRightImages J).inverseImage (R j)) :
    relativeCells.{w} (EvaluationFamily.generators L J) ≤
      EvaluationFamily.detected R (weakEquivalences C) := by
  have hgen : J ≤ trivialCofibrations C :=
    J.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J).symm.le
  intro A B f hf j
  have hmap : EvaluationFamily.generators L J ≤ (tensorRightImages J).inverseImage (R j) :=
    iSup_le (fun i ↦ hfree i j)
  exact ((relativeCells_map_le (R j) _ _ hmap).trans
    (MorphismProperty.monotone_inverseImage _ (tensorCells_le_weakEquivalences J hgen))) f hf

omit [ModelCategory C] [HasMonoidAxiom.{w} C]
  [∀ i, PreservesColimitsOfSize.{w, w} (R i)]
  [∀ i, PreservesColimitsOfShape WalkingSpan (R i)] in
/-- A natural free/evaluation tensor formula supplies the generator test.
No cofibrancy of the coefficient objects is needed. -/
lemma freeGenerators_tensor_images [BraidedCategory C] (H : ι → ι → C)
    (e : ∀ i j, L i ⋙ R j ≅ tensorLeft (H i j)) :
    ∀ i j, J.strictMap (L i) ≤ (tensorRightImages J).inverseImage (R j) := by
  intro i j A B f hf
  cases hf with
  | map hf =>
    have h := J.map_mem_map (L i ⋙ R j) _ hf
    rw [J.map_eq_of_iso (e i j ≪≫ BraidedCategory.tensorLeftIsoTensorRight (H i j))] at h
    exact (le_iSup (fun X : C ↦ J.map (tensorRight X)) (H i j)) _ h

variable [HasFiniteLimits D] [HasFiniteColimits D]
  (adj : ∀ i, L i ⊣ R i)
  [(EvaluationFamily.generators L I).HasSmallObjectArgument.{w}]
  [(EvaluationFamily.generators L J).HasSmallObjectArgument.{w}]

/-- The many-object right-induced model follows from the monoid axiom and the
free-generator tensor formula. Small-object arguments remain concrete inputs. -/
@[instance_reducible]
def modelCategory
    (hfree : ∀ i j, J.strictMap (L i) ≤ (tensorRightImages J).inverseImage (R j)) :
    ModelCategory D :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCategory L R adj I J (freeCells_acyclic L R I J hfree)

lemma modelCategory_weakEquivalences (hfree) :
    @weakEquivalences D _ (modelCategory L R I J adj hfree).categoryWithWeakEquivalences =
      EvaluationFamily.detected R (weakEquivalences C) := rfl

lemma modelCategory_fibrations (hfree) :
    @fibrations D _ (modelCategory L R I J adj hfree).categoryWithFibrations =
      EvaluationFamily.detected R (fibrations C) := rfl

lemma modelCategory_generated (hfree) :
    let := modelCategory L R I J adj hfree
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (EvaluationFamily.generators L I) (EvaluationFamily.generators L J) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCategory_generated L R adj I J (freeCells_acyclic L R I J hfree)

/-- Many-object transfer with the natural free/evaluation formula as concrete input. -/
@[instance_reducible]
def modelCategoryOfTensorFormula [BraidedCategory C] (H : ι → ι → C)
    (e : ∀ i j, L i ⋙ R j ≅ tensorLeft (H i j)) : ModelCategory D :=
  modelCategory L R I J adj (freeGenerators_tensor_images L R J H e)

lemma evaluation_isRightQuillen (hfree) (i : ι) :
    let := modelCategory L R I J adj hfree
    IsRightQuillen (R i) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.evaluation_isRightQuillen L R adj I J (freeCells_acyclic L R I J hfree) i

lemma free_isLeftQuillen (hfree) (i : ι) :
    let := modelCategory L R I J adj hfree
    IsLeftQuillen (L i) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.free_isLeftQuillen L R adj I J (freeCells_acyclic L R I J hfree) i

end SerrePositivity.ManyObjectModelTransfer
