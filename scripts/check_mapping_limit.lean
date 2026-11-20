import SerrePositivity.HomotopicalAlgebra.Diagram.FrameMappingLimit
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
  (cosimplicialHom cosimplicialHomMap)

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]

-- No model or enrichment assumptions are needed for the explicit limit cone.
example (A : SimplexCategory ⥤ K ⥤ C) (Y : C) : IsLimit (MappingLimit.cone K A Y) :=
  MappingLimit.coneIsLimit K A Y

example (A : SimplexCategory ⥤ K ⥤ C) (Y : C) : HasLimit (MappingLimit.lifted K A Y) :=
  MappingLimit.hasLimit K A Y

-- The actual isomorphism is natural in the target and the cosimplicial diagram.
example (A : SimplexCategory ⥤ K ⥤ C) {Y Z : C} (f : Y ⟶ Z)
    [HasLimit (MappingLimit.lifted K A Y)] [HasLimit (MappingLimit.lifted K A Z)] :
    (cosimplicialHom A).map ((Functor.const K).map f) ≫ (MappingLimit.iso K A Z).hom =
      (MappingLimit.iso K A Y).hom ≫ lim.map (MappingLimit.mapTarget K A f) :=
  MappingLimit.iso_target_naturality K A f

example {A B : SimplexCategory ⥤ K ⥤ C} (a : A ⟶ B) (Y : C)
    [HasLimit (MappingLimit.lifted K A Y)] [HasLimit (MappingLimit.lifted K B Y)] :
    (cosimplicialHomMap a).app ((Functor.const K).obj Y) ≫ (MappingLimit.iso K A Y).hom =
      (MappingLimit.iso K B Y).hom ≫ lim.map (MappingLimit.mapSource K (Y := Y) a) :=
  MappingLimit.iso_source_naturality K a

open HomotopicalAlgebra
variable [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

-- This is the SAME frame diagram used by the pointwise RMap comparison.
-- The ordinary limit exists by construction, rather than as a new input.
example (F : (K ⥤ C)ᵒᵖ) (Y : C) :
    let := FrameMappingLimit.hasLimit K I J fib F Y
    Nonempty ((((ColimitMapComparison.diagramHom K I J fib).obj F).obj Y) ≅
      limit (FrameMappingLimit.liftedFrameDiagram K I J fib F Y)) := by
  let := FrameMappingLimit.hasLimit K I J fib F Y
  exact ⟨FrameMappingLimit.diagramHomLimitIso K I J fib F Y⟩

example : PointwiseMappingComparison.frameDiagram K I J fib ≅
    FrameMappingLimit.evaluatedHom K I J fib := FrameMappingLimit.evaluatedHomIso K I J fib

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.MappingLimit,
    `SerrePositivity.HomotopicalAlgebra.Diagram.FrameMappingLimit]
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
  logInfo m!"Actual mapping limit audit passed: {count} declarations in {seen.size} modules."
