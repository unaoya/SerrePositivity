import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Smith

variable {C : Type u} [Category.{v} C]

example [HasColimitsOfSize.{w, w} C] (I : MorphismProperty C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i : I.toSet, IsCardinalPresentable i.val.left κ]
    [∀ i : I.toSet, IsCardinalPresentable i.val.right κ]
    {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
    {F : J ⥤ Arrow C} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, I.rlp (F.obj j).hom) : I.rlp c.pt.hom :=
  AccessibleLiftingClosure.rlp_of_isColimit I κ hc hF

example [ModelCategory C]
    (d : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C)) (f : Arrow C) :
    weakEquivalences C f.hom ↔ trivialFibrations C (d.p.app f) :=
  WeakEquivalenceFilteredColimits.weakEquivalence_iff_rightFactor d f

-- This consumer assumes neither filtered-colimit closure nor accessibility of W.
example [ModelCategory C] [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      HasCardinalFilteredColimits.{w} (arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
      (arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ :=
  exists_weakEquivalence_filtered_colimits I J

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLiftingClosure,
    `SerrePositivity.HomotopicalAlgebra.Smith.WeakEquivalenceFilteredColimits]
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
  if modules.size != expected.size then throwError "Not all weak-equivalence colimit modules were audited"
  logInfo m!"Weak-equivalence filtered-colimit audit passed: {count} declarations in 2 modules, standard axioms only."
