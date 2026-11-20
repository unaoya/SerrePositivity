import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleRightClass
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Smith

variable {C : Type u} [Category.{v} C]

-- This theorem constructs a small presentable generating family from final inputs.
example [IsLocallyPresentable.{w} C] (I : MorphismProperty C) [I.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory (arrowProperty I.rlp).FullSubcategory κ ∧
      (arrowInclusion I.rlp).IsCardinalAccessible κ :=
  exists_accessible_right_lifting_class I

example [ModelCategory C] [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory (arrowProperty (trivialFibrations C)).FullSubcategory κ ∧
      (arrowInclusion (trivialFibrations C)).IsCardinalAccessible κ := by
  have : I.IsSmall.{w} := by
    obtain ⟨μ, hμ, hb, hI⟩ := MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := I)
    exact SmallObject.isSmall I μ
  have h := exists_accessible_right_lifting_class I
  have hI : I.rlp = trivialFibrations C :=
    SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)
  rw [hI] at h
  exact h

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleRightClass do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Accessible right-class module was not audited"
  logInfo m!"Accessible right-class audit passed: {count} declarations, standard axioms only."
