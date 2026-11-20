import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveBifunctor
import SerrePositivity.HomotopicalAlgebra.Enriched.TensorCotensor
import Lean.Util.CollectAxioms

noncomputable section
universe w v u vV uV
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.PointwiseAdjunction

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  {V : Type uV} [Category.{vV} V] [ModelCategory V]

-- The actual parametrized adjunction lifts to the ordinary diagram category.
example (F : V ⥤ C ⥤ C) (G : Vᵒᵖ ⥤ C ⥤ C) (adj : F ⊣₂ G) :
    pointwise K F ⊣₂ pointwise K G := SerrePositivity.PointwiseAdjunction.adjunction K adj

-- Only the original two-variable Quillen condition is input; no diagram
-- cofibration is assumed to be determined objectwise.
example (F : V ⥤ C ⥤ C) (G : Vᵒᵖ ⥤ C ⥤ C) (adj : F ⊣₂ G) [IsQuillenBifunctor F] :
    let := SerrePositivity.DiagramModel.Projective.modelCategory K I J
    IsQuillenBifunctor (pointwise K F) :=
  SerrePositivity.DiagramModel.Projective.pointwise_isQuillenBifunctor K I J F G adj

-- This specializes directly to the previously represented enriched
-- tensor/cotensor data over an arbitrary enriching model category V.
example [MonoidalCategory V] [EnrichedOrdinaryCategory V C]
    (S : SerrePositivity.Enriched.TensorCotensor V C) [IsQuillenBifunctor S.tensor] :
    let := SerrePositivity.DiagramModel.Projective.modelCategory K I J
    IsQuillenBifunctor (pointwise K S.tensor) :=
  SerrePositivity.DiagramModel.Projective.pointwise_isQuillenBifunctor K I J
    S.tensor S.cotensor S.tensorCotensor

-- Evaluation retains the actual pullback-hom comparison map.
example (G : Vᵒᵖ ⥤ C ⥤ C) {A B : V} (i : A ⟶ B) {X Y : K ⥤ C} (p : X ⟶ Y)
    (sq : (pointwise K G).PullbackObjObj i p) (k : K) :
    (evaluatePullbackObjObj K G i p sq k).π = sq.π.app k := rfl

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.Adjunction.Comparison,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveBifunctor]
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
  logInfo m!"Projective bifunctor audit passed: {count} declarations in {seen.size} modules."
