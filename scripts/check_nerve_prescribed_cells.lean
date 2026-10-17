import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vD uD vC uC
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel
open SerrePositivity.NerveSimplexEndpoint

section PureAssembly
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type uC} [Category.{vC} C]
  (F G : J ⥤ C) (n : ℕ)
  (old : Reedy.lowerInclusion r n ⋙ F ⟶ Reedy.lowerInclusion r n ⋙ G)
  (cells : Reedy.PrescribedLowerStep.Data r F G n old)

-- No model or boundary-limit assumptions, and no degree-injectivity assumption.
example : Functor.whiskerLeft (Reedy.lowerMap r (Nat.le_succ n)) cells.assemble = old :=
  cells.assemble_restrict
example (j : J) (hj : r.deg j = n) :
    cells.assemble.app ⟨j, hj ▸ Nat.lt_succ_self n⟩ = cells.hom j hj := cells.assemble_new j hj

-- Local direct/inverse conditions imply full naturality, even between same-degree objects.
example {j k : Reedy.Lower r (n + 1)} (f : j ⟶ k) :
    F.map f.hom ≫ cells.assemble.app k = cells.assemble.app j ≫ G.map f.hom :=
  cells.assemble.naturality f
end PureAssembly

section ChosenEdgesAndTriangles
variable {D : Type uD} [Category.{vD} D] [ModelCategory SSet.{v}] (F : D ⥤ SSet.{v})
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (points : ∀ d, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d)
  (edges : NervePrescribedCells.Data F 1 (NerveLowerExtension.vertices F points))
  (triangles : NervePrescribedCells.Data F 2
    (NervePrescribedCells.assemble F 1 (NerveLowerExtension.vertices F points) edges))

private abbrev old₂ :=
  NervePrescribedCells.assemble F 1 (NerveLowerExtension.vertices F points) edges
private abbrev whole := NervePrescribedCells.extend F 2 (old₂ F points edges) triangles hp hcof

-- Both layers are supplied independently, with only the stated local boundary conditions.
example (c : ComposableArrows D 2) :
    (whole F hp hcof points edges triangles).app (ofChain c) = triangles.hom (ofChain c) rfl :=
  NervePrescribedCells.extend_chain F 2 (old₂ F points edges) triangles hp hcof c

example {x y : D} (f : x ⟶ y) :
    (whole F hp hcof points edges triangles).app (ofChain (ComposableArrows.mk₁ f)) =
      edges.hom (ofChain (ComposableArrows.mk₁ f)) rfl := by
  exact (NervePrescribedCells.extend_old F 2 (old₂ F points edges) triangles hp hcof
    ⟨ofChain (ComposableArrows.mk₁ f), Nat.lt_succ_self 1⟩).trans
      (NervePrescribedCells.assemble_new F 1 (NerveLowerExtension.vertices F points) edges
        (ofChain (ComposableArrows.mk₁ f)) rfl)

example (d : D) : (whole F hp hcof points edges triangles).app
    (ofChain (ComposableArrows.mk₀ d)) = points d := by
  exact (NervePrescribedCells.extend_old F 2 (old₂ F points edges) triangles hp hcof
    ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_succ 1⟩).trans
      ((NervePrescribedCells.assemble_old F 1 (NerveLowerExtension.vertices F points) edges
        ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩).trans
          (NerveLowerExtension.vertices_component F points d))

-- One global system retains all old cells and respects every external simplex operator.
example {s t : Index D} (f : s ⟶ t) :
    SSet.stdSimplex.map (operator f) ≫ (whole F hp hcof points edges triangles).app t =
      (whole F hp hcof points edges triangles).app s ≫ F.map (endpointMap f) :=
  NerveCoherentFamily.compatibility F (whole F hp hcof points edges triangles) f
end ChosenEdgesAndTriangles

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.PrescribedLowerStep,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NervePrescribedCells]
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
    throwError "Some mixed choice modules were not audited"
  logInfo m!"Prescribed coherent cells audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
