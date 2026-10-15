import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftWeakEquivalence
import Lean.Util.CollectAxioms

noncomputable section
universe w v u v' u'
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel.UniverseLift

-- Pure comparisons impose no model structure or universe ordering.
example (n : ℕ) :
    Arrow.mk (SSet.uliftFunctor.{w, v}.map (SSet.boundary.{v} n).ι) ≅
      Arrow.mk (SSet.boundary.{max v w} n).ι := boundaryArrowIso n

example (n : ℕ) (i : Fin (n + 1)) :
    Arrow.mk (SSet.uliftFunctor.{w, v}.map (SSet.horn.{v} n i).ι) ≅
      Arrow.mk (SSet.horn.{max v w} n i).ι := hornArrowIso n i

example : PreservesColimitsOfSize.{v, v} SSet.uliftFunctor.{w, v} := inferInstance
example : PreservesColimitsOfShape WalkingSpan SSet.uliftFunctor.{w, v} := inferInstance

example {X Y : SSet.{v}} (p : X ⟶ Y) :
    SSet.modelCategoryQuillen.J.{max v w}.rlp (SSet.uliftFunctor.{w, v}.map p) ↔
      SSet.modelCategoryQuillen.J.{v}.rlp p := horn_rightClass_iff p

section General
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) [F.Full] [F.Faithful]

example {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (F.map i) (F.map p) ↔ HasLiftingProperty i p :=
  SerrePositivity.ModelGeneration.hasLiftingProperty_map_iff F i p

example [ModelCategory C] [ModelCategory D] [SerrePositivity.Quillen.IsRightQuillen F]
    (hc : cofibrations C ≤ (cofibrations D).inverseImage F)
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences D (F.map f)) : weakEquivalences C f :=
  SerrePositivity.Quillen.weakEquivalence_of_map F hc f hf
end General

variable [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcof' : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfib' : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

example : SerrePositivity.Quillen.IsLeftQuillen SSet.uliftFunctor.{w, v} :=
  isLeftQuillen.{w, v} hcof hfib hcof' hfib'

example : SerrePositivity.Quillen.IsRightQuillen SSet.uliftFunctor.{w, v} :=
  isRightQuillen.{w, v} hcof hfib hcof' hfib'

-- Arbitrary maps: neither endpoint is assumed cofibrant, Kan or fibrant.
example {X Y : SSet.{v}} (f : X ⟶ Y) :
    weakEquivalences SSet.{max v w} (SSet.uliftFunctor.{w, v}.map f) ↔
      weakEquivalences SSet.{v} f := weakEquivalences_map_iff.{w, v} hcof hfib hcof' hfib' f

-- An actual arrow isomorphism in the common universe suffices to compare
-- weak-equivalence tests in two independent smaller universes.
example [ModelCategory SSet.{w}]
    (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    {X Y : SSet.{v}} (f : X ⟶ Y) {X' Y' : SSet.{w}} (g : X' ⟶ Y')
    (e : Arrow.mk (SSet.uliftFunctor.{w, v}.map f) ≅
      Arrow.mk (SSet.uliftFunctor.{v, w}.map g)) :
    weakEquivalences SSet.{v} f ↔ weakEquivalences SSet.{w} g :=
  weakEquivalences_iff_of_liftedArrowIso hcof hfib hcof' hfib' hcofW hfibW f g e

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Transfer.FullyFaithfulLifting,
    `SerrePositivity.HomotopicalAlgebra.Quillen.FullyFaithfulReflection,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLift,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftModel,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftWeakEquivalence]
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
  logInfo m!"Simplicial universe lift audit passed: {count} declarations in {seen.size} modules."
