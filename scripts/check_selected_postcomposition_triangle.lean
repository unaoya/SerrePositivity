import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y W V : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) (h : W ⟶ V)

-- Compatibility is an output from actual selected edge endpoints, not input.
example : BoundaryGluing.StandardCompatible
    (CoherentLiftPostComposition.faces hcof hfib X Y W V f g h) :=
  CoherentLiftPostComposition.faces_compatible hcof hfib X Y W V f g h

-- The three faces are the pre-existing choices, with their actual transports.
-- In particular the direct g≫h comparison is not replaced by a new edge.
example :
    SSet.stdSimplex.δ (0 : Fin 3) ≫ CoherentLiftPostComposition.triangle hcof hfib X Y W V f g h =
        CoherentLiftPostComposition.secondEdge hcof hfib X Y W V f g h ∧
      SSet.stdSimplex.δ (1 : Fin 3) ≫ CoherentLiftPostComposition.triangle hcof hfib X Y W V f g h =
        postEdge hcof hfib X Y V f (g ≫ h) ∧
      SSet.stdSimplex.δ (2 : Fin 3) ≫ CoherentLiftPostComposition.triangle hcof hfib X Y W V f g h =
        CoherentLiftPostComposition.firstEdge hcof hfib X Y W V f g h :=
  ⟨CoherentLiftPostComposition.triangle_face hcof hfib X Y W V f g h 0,
    CoherentLiftPostComposition.triangle_face hcof hfib X Y W V f g h 1,
    CoherentLiftPostComposition.triangle_face hcof hfib X Y W V f g h 2⟩

-- All strict lift vertices are fixed throughout the whole triangle.
example : vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f (g ≫ h))
          (CoherentLiftPostComposition.triangle hcof hfib X Y W V f g h) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ postBoundary X Y V f (g ≫ h) :=
  CoherentLiftPostComposition.triangle_fixed_boundary hcof hfib X Y W V f g h

-- The actual Kan action restricts to the retained choices in every target Z,
-- using the same selected triangle, with no fibrancy or source FF assumption.
example (Z : C) (t : CoherentLiftTuples.obj X Y f ⊗
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ (cosimplicialHom V.resolution.obj).obj Z)
    (k : Fin 3) :
    CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k ≫
        KanLiftAction.parameterized hcof hfib X V (f ≫ (g ≫ h).base) Z
          (RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f (g ≫ h))
            (CoherentLiftPostComposition.triangle hcof hfib X Y W V f g h)) t =
      KanLiftAction.parameterized hcof hfib X V (f ≫ (g ≫ h).base) Z
        (RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f (g ≫ h))
          (CoherentLiftPostComposition.faces hcof hfib X Y W V f g h k))
        ((CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k) ≫ t) :=
  CoherentLiftPostComposition.triangle_action_face hcof hfib X Y W V f g h Z t k

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceMaps,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition]
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
    throwError "Some selected triangle modules were not audited"
  logInfo m!"Selected postcomposition triangle audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
