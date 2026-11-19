import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Smith

-- Proved inverse-image closure, with independent category and hom universes.
example {C : Type u₁} [Category.{v₁} C] [IsLocallyPresentable.{w} C]
    {E : Type u₂} [Category.{v₂} E] [IsLocallyPresentable.{w} E]
    (I : MorphismProperty E) [I.IsSmall.{w}] (F : C ⥤ Arrow E) [F.IsAccessible.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory ((arrowProperty I.rlp).inverseImage F).FullSubcategory κ ∧
      (((arrowProperty I.rlp).inverseImage F).ι).IsCardinalAccessible κ :=
  exists_accessible_rightClass_inverseImage I F

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  [IsLocallyPresentable.{w} C] (I J : MorphismProperty C)
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

include I J in
-- Full A0/A1 consumer: no assumed accessibility of W, replacements, or factorizations.
example :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : AccessibleModelFactorizations C κ,
        d.cofibrationData.Z.IsCardinalAccessible κ ∧
        d.fibrationData.Z.IsCardinalAccessible κ ∧
        (AccessibleFactorization.leftFactor d.cofibrationData).IsCardinalAccessible κ ∧
        (AccessibleFactorization.rightFactor d.cofibrationData).IsCardinalAccessible κ ∧
        (AccessibleFactorization.leftFactor d.fibrationData).IsCardinalAccessible κ ∧
        (AccessibleFactorization.rightFactor d.fibrationData).IsCardinalAccessible κ ∧
        d.Q.IsCardinalAccessible κ ∧ d.R.IsCardinalAccessible κ ∧
        IsCardinalAccessibleCategory (arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
        (arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ := by
  have := locallyPresentable_hasColimits (C := C)
  obtain ⟨κ, hκ, d, hW, hι⟩ := exists_accessible_model_and_weakEquivalences I J
  exact ⟨κ, hκ, d, d.cofibrationAccessible, d.fibrationAccessible,
    d.cofibration_left_isCardinalAccessible, d.cofibration_right_isCardinalAccessible,
    d.fibration_left_isCardinalAccessible, d.fibration_right_isCardinalAccessible,
    d.Q_isCardinalAccessible, d.R_isCardinalAccessible, hW, hι⟩

include I J in
example : IsAccessibleCategory.{w} (arrowProperty (weakEquivalences C)).FullSubcategory ∧
    (arrowInclusion (weakEquivalences C)).IsAccessible.{w} :=
  ⟨weakEquivalences_isAccessibleCategory I J, weakEquivalences_inclusion_isAccessible I J⟩

include I J in
example : SolutionSetCondition.{w} (arrowInclusion (weakEquivalences C)) :=
  weakEquivalences_solutionSetCondition I J

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Smith.PresentableOverIteration,
    `SerrePositivity.HomotopicalAlgebra.Smith.LiftingColimitRefinement,
    `SerrePositivity.HomotopicalAlgebra.Smith.RightClassInverseImageCover,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleRightClassInverseImage,
    `SerrePositivity.HomotopicalAlgebra.Smith.WeakEquivalencesAccessible]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if modules.size != expected.size then throwError "Not all A1 implementation modules were audited"
  logInfo m!"Weak-equivalence accessibility audit passed: {count} declarations in 5 modules, standard axioms only."
