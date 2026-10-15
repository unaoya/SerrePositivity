import SerrePositivity.HomotopicalAlgebra.Localization.SmallHomTests
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomAccessible
import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleWeakEquivalenceInverseImage
import Lean.Util.CollectAxioms

noncomputable section
universe w t v u vE uE
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

-- An isomorphism of actual bifunctors is natural in the whole source frame.
example (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C) {X Y : C} (f : X ⟶ Y) (Z : C) :
    Arrow.mk (SSet.uliftFunctor.{v, w}.map
        (((SmallHomComparison.hom Q R).map f.op).app Z)) ≅
      Arrow.mk (SSet.uliftFunctor.{w, v}.map (((resolutionHom Q R).map f.op).app Z)) :=
  SmallHomComparison.sourceArrowIso Q R f Z

-- No SSet model is required for the accessibility package. Only original
-- combinatorial inputs and the fixed small family of arrows are supplied.
example (I J : MorphismProperty C) [ModelGeneration.CofibrantlyGenerated.{w} I J]
    {ι : Type t} [Small.{w} ι] (s : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : Smith.AccessibleModelFactorizations C κ,
        IsCardinalAccessibleCategory (Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
        (Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ ∧
        (∀ i, ((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj
            (Opposite.op (s i).left)).IsCardinalAccessible κ ∧
          ((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj
            (Opposite.op (s i).right)).IsCardinalAccessible κ) ∧
        (MappingTests.family (SmallHomComparison.chosenHom d.cofibrationData d.fibrationData)
          s).IsCardinalAccessible κ := SmallHomComparison.exists_accessible_mapping_tests I J s

variable [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

example (S : MorphismProperty C) :
    Bousfield.smallLocalObjects.{w, v, u} cof fib S = Bousfield.localObjects cof fib S :=
  Bousfield.smallLocalObjects_eq.{w, v, u} cof fib hcofW hfibW hcofV hfibV hcofB hfibB S

example (S : MorphismProperty C) :
    Bousfield.smallLocalEquivalences.{w, v, u} cof fib S = Bousfield.localEquivalences cof fib S :=
  Bousfield.smallLocalEquivalences_eq.{w, v, u} cof fib hcofW hfibW hcofV hfibV hcofB hfibB S

section InverseImage
variable {B : Type u} [Category.{v} B] [IsLocallyPresentable.{w} B]
  {E : Type uE} [Category.{vE} E] [ModelCategory E] [IsLocallyPresentable.{w} E]

-- The source B need not be a model category. No assumption that arbitrary
-- accessible full images or arbitrary inverse images are accessible is used.
example (I J : MorphismProperty E) [ModelGeneration.CofibrantlyGenerated.{w} I J]
    (F : B ⥤ Arrow E) [F.IsAccessible.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory
        ((Smith.arrowProperty (weakEquivalences E)).inverseImage F).FullSubcategory κ ∧
      (((Smith.arrowProperty (weakEquivalences E)).inverseImage F).ι).IsCardinalAccessible κ :=
  Smith.exists_accessible_weakEquivalence_inverseImage I J F
end InverseImage

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomAccessible,
    `SerrePositivity.HomotopicalAlgebra.Localization.SmallHomTests,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleWeakEquivalenceInverseImage]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Small-Hom locality audit passed: {count} declarations in {seen.size} modules."
