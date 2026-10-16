import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel.StrictValueObstruction

section FixedValueObstructionAndChangedValueRepair
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
-- A concrete pair of weakly equivalent Kan complexes is not an isomorphic pair.
example : SSet.KanComplex (point.{v}) := point_kanComplex
example : SSet.KanComplex (complex.{v}) := complex_kanComplex hfib
example : trivialFibrations SSet.{v} toPoint.{v} := toPoint_trivialFibration
example : ¬ Nonempty (complex.{v} ≅ point) := not_iso_point hcof
example : ¬ Subsingleton ((complex.{v}).obj (Opposite.op (SimplexCategory.mk 0))) :=
  complex_not_subsingleton_vertices hcof
example (F : Base ⥤ SSet.{v}) (e : ∀ b, F.obj b ≅ value.{v} b) : False :=
  no_fixed_value_lift hcof F e
-- The full presentation projection satisfies every stated smallness/invariance condition.
example : projection.{v}.Full := inferInstance
example (b : Presentations.{v}) : SSet.KanComplex (diagram.obj b) := value_kanComplex hfib b
example {b c : Presentations.{v}} (f : b ⟶ c) :
    weakEquivalences SSet.{v} (diagram.map f) := diagram_map_weakEquivalence f
example (F : Base ⥤ SSet.{v}) : ¬ Nonempty (diagram.{v} ≅ projection.{v} ⋙ F) :=
  no_isomorphic_descent hcof F
-- A natural weak equivalence is available when the strict values may change.
example : diagram.{v} ⟶ projection.{v} ⋙ repair.{v} := changedValueComparison
example (b : Presentations.{v}) :
    weakEquivalences SSet.{v} (changedValueComparison.app b) :=
  changedValueComparison_weakEquivalence b
variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{v})]
example {b c : Presentations.{v}} (f g : b ⟶ c) :
    L.map (diagram.map f) = L.map (diagram.map g) := parallel_maps_localize_equal L f g
example (b : Base) : (localized L).obj b = L.obj (value.{v} b) := rfl
example {b c d : Base} (f : b ⟶ c) (g : c ⟶ d) :
    (localized L).map (f ≫ g) = (localized L).map f ≫ (localized L).map g :=
  (localized L).map_comp f g
example : localized L ≅ repair.{v} ⋙ L := repairComparisonIso L
example : IsIso (Functor.whiskerRight (changedValueComparison.{v}) L) := inferInstance
end FixedValueObstructionAndChangedValueRepair

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.StrictValueObstruction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.StrictValueDescentCounterexample,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.StrictValuePresentationCounterexample]
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
  unless modules.size == expected.size do
    throwError "Some strict-value descent modules were not audited"
  logInfo m!"Strict-value descent counterexample audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
