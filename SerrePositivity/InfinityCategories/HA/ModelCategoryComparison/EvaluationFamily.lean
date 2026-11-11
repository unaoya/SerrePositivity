module
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap
public import SerrePositivity.HomotopicalAlgebra.Simplicial.EvaluationMorphismProperties
public import SerrePositivity.HomotopicalAlgebra.Transfer.Recognition
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic


/-!
概要：評価関手の族で検出するモデル構造と Quillen 随伴。
方針：純粋な射の性質は Transfer.EvaluationFamily に置き、モデル構造の移入をここで構成する。
規約：元の宣言名・型・証明を保存する。
使われ方：射影モデル構造と多対象の移入。
-/

@[expose] public section
universe w t u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {ι : Type t} (L : ι → C ⥤ D) (R : ι → D ⥤ C) (adj : ∀ i, L i ⊣ R i)

variable [ModelCategory C] [HasFiniteLimits D] [HasFiniteColimits D]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [(_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L I).HasSmallObjectArgument.{w}]
  [(_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L J).HasSmallObjectArgument.{w}]

include adj in
/-- Transfer to the actual module category using all free/evaluation adjunctions. -/
@[instance_reducible]
def modelCategory
    (hacyclic : SerrePositivity.Quillen.relativeCells.{w} (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L J) ≤
      _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected R (weakEquivalences C)) : ModelCategory D := by
  letI := _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detectedFibrations R
  letI := _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detectedWeakEquivalences R
  letI := _root_.SerrePositivity.ModelGeneration.EvaluationFamily.generatedCofibrations L I
  have : (weakEquivalences D).HasTwoOutOfThreeProperty :=
    inferInstanceAs ((_root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected R (weakEquivalences C)).HasTwoOutOfThreeProperty)
  have : (weakEquivalences D).IsStableUnderRetracts :=
    inferInstanceAs ((_root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected R (weakEquivalences C)).IsStableUnderRetracts)
  have hI : (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L I).rlp = trivialFibrations D := by
    rw [_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_rlp L R adj, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)]
    exact _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected_inf R _ _
  have hJ : (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L J).rlp = fibrations D := by
    rw [_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_rlp L R adj, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_J (I := I) (J := J)]
    rfl
  exact _root_.SerrePositivity.ModelGeneration.modelCategoryOfRecognition (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L I) (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L J) hI hJ rfl
    (_root_.SerrePositivity.ModelGeneration.generatedLeft_le_of_cells_le _ _ hacyclic)

lemma modelCategory_weakEquivalences (hacyclic) :
    @weakEquivalences D _ (modelCategory L R adj I J hacyclic).categoryWithWeakEquivalences =
      _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected R (weakEquivalences C) := rfl

lemma modelCategory_fibrations (hacyclic) :
    @fibrations D _ (modelCategory L R adj I J hacyclic).categoryWithFibrations =
      _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected R (fibrations C) := rfl

lemma modelCategory_generated (hacyclic) :
    let := modelCategory L R adj I J hacyclic
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L I) (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L J) := by
  let := modelCategory L R adj I J hacyclic
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · rw [_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_rlp L R adj, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)]
    exact _root_.SerrePositivity.ModelGeneration.EvaluationFamily.detected_inf R _ _
  · rw [_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators_rlp L R adj, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_J (I := I) (J := J)]
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
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
      (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L I) (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L J),
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L I) (_root_.SerrePositivity.ModelGeneration.EvaluationFamily.generators L J)⟩

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
