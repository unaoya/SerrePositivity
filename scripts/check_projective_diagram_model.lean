import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen
import Lean.Util.CollectAxioms

noncomputable section
universe w v u vH uH
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- Final existence uses the original combinatorial model, not a diagram
-- model axiom, transfer acyclicity input, or extra image smallness input.
example : Nonempty (ModelCategory (K ⥤ C)) := ⟨Projective.modelCategory K I J⟩

example {F G : K ⥤ C} (f : F ⟶ G) :
    let := Projective.modelCategory K I J
    WeakEquivalence f ↔ ∀ k, WeakEquivalence (f.app k) :=
  Projective.weakEquivalence_iff_objectwise K I J f

example {F G : K ⥤ C} (f : F ⟶ G) :
    let := Projective.modelCategory K I J
    Fibration f ↔ ∀ k, Fibration (f.app k) :=
  Projective.fibration_iff_objectwise K I J f

example :
    let := Projective.modelCategory K I J
    SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w}
      (Projective.generators K I) (Projective.generators K J) :=
  Projective.modelCategory_generated K I J

-- This is the actual chosen colimit functor, with no tensor assumptions.
example :
    let := Projective.modelCategory K I J
    let := SerrePositivity.Smith.locallyPresentable_hasColimits (C := C)
    SerrePositivity.Quillen.IsLeftQuillen (colim : (K ⥤ C) ⥤ C) :=
  Projective.colimit_isLeftQuillen K I J

example {H : Type uH} [Category.{vH} H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] :
    let := Projective.modelCategory K I J
    let := SerrePositivity.Smith.locallyPresentable_hasColimits (C := C)
    ((colim : (K ⥤ C) ⥤ C) ⋙ L).HasPointwiseLeftDerivedFunctor
      (weakEquivalences (K ⥤ C)) :=
  Projective.hasPointwiseLeftDerivedColimit K I J L

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.Projective,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen]
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
  logInfo m!"Projective diagram model audit passed: {count} declarations in {seen.size} modules."
