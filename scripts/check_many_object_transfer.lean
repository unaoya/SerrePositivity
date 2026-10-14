import SerrePositivity.HomotopicalAlgebra.Foundations
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe w t u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.ModelGeneration
open SerrePositivity.ManyObjectModelTransfer

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {ι : Type t}
  [MonoidalCategory C] [BraidedCategory C] [ModelCategory C] [HasMonoidAxiom.{w} C]
  [HasFiniteLimits D] [HasFiniteColimits D]
  (L : ι → C ⥤ D) (R : ι → D ⥤ C) (adj : ∀ i, L i ⊣ R i)
  [∀ i, PreservesColimitsOfSize.{w, w} (R i)]
  [∀ i, PreservesColimitsOfShape WalkingSpan (R i)]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  [(EvaluationFamily.generators L I).HasSmallObjectArgument.{w}]
  [(EvaluationFamily.generators L J).HasSmallObjectArgument.{w}]
  (H : ι → ι → C) (e : ∀ i j, L i ⋙ R j ≅ tensorLeft (H i j))

-- D starts without a model structure, and its objects are not assumed to be ordinary diagrams.
-- In particular the Hom coefficients H i j are not assumed cofibrant.
example : ModelCategory D := modelCategoryOfTensorFormula L R I J adj H e

example : relativeCells.{w} (EvaluationFamily.generators L J) ≤
    EvaluationFamily.detected R (weakEquivalences C) :=
  freeCells_acyclic L R I J (freeGenerators_tensor_images L R J H e)

example : @weakEquivalences D _
    (modelCategoryOfTensorFormula L R I J adj H e).categoryWithWeakEquivalences =
      EvaluationFamily.detected R (weakEquivalences C) := rfl

example : @fibrations D _ (modelCategoryOfTensorFormula L R I J adj H e).categoryWithFibrations =
    EvaluationFamily.detected R (fibrations C) := rfl

example : let := modelCategoryOfTensorFormula L R I J adj H e
    CofibrantlyGenerated.{w} (EvaluationFamily.generators L I) (EvaluationFamily.generators L J) :=
  modelCategory_generated L R I J adj (freeGenerators_tensor_images L R J H e)

example (i : ι) : let := modelCategoryOfTensorFormula L R I J adj H e
    IsRightQuillen (R i) :=
  evaluation_isRightQuillen L R I J adj (freeGenerators_tensor_images L R J H e) i

example (i : ι) : let := modelCategoryOfTensorFormula L R I J adj H e
    IsLeftQuillen (L i) :=
  free_isLeftQuillen L R I J adj (freeGenerators_tensor_images L R J H e) i

example : let := modelCategoryOfTensorFormula L R I J adj H e
    (cofibrations D).HasFunctorialFactorization (trivialFibrations D) ∧
      (trivialCofibrations D).HasFunctorialFactorization (fibrations D) :=
  EvaluationFamily.functorialFactorizations L R adj I J
    (freeCells_acyclic L R I J (freeGenerators_tensor_images L R J H e))

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationFamily,
        `SerrePositivity.HomotopicalAlgebra.Monoidal.ManyObjectTransfer].contains
        env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No many-object transfer declarations audited"
  logInfo m!"Many-object transfer audit passed: {count} declarations, standard axioms only."
