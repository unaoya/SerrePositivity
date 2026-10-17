import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.NerveSimplexEndpoint

section GeneralHigherBoundaries
variable {D : Type uD} [Category.{vD} D] [ModelCategory SSet.{v}]
  (F : D ⥤ SSet.{v}) {n : ℕ}
  (faces : Fin (n + 3) → NerveParameterExtension.System F
    (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1))))
  (hf : NerveBoundaryExtension.Compatible F faces)
  (old : ∀ d, SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 2)) ⟶ F.obj d)
  (hfaces : ∀ (k : Fin (n + 3)) (s : Reedy.Lower (NerveCoherentFamily.reedy D) 1),
    (faces k).app s.obj = SSet.stdSimplex.isTerminalObj₀.from _ ≫
      RelativeChoiceSpace.name (SSet.stdSimplex.δ k ≫ old (endpoint s.obj)))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))

-- Arbitrary higher simplices are retained whole, with all preselected whole facets.
example (d : D) : NerveParameterExtension.evaluate F
    (NerveBoundaryExtension.extend F faces hf old hfaces hcof hfib hp) d = old d :=
  NerveBoundaryExtension.extend_evaluate _ _ _ _ _ _ _ _ d

example (k : Fin (n + 3)) : NerveBoundaryExtension.extend F faces hf old hfaces hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ k)) = faces k :=
  NerveBoundaryExtension.extend_face _ _ _ _ _ _ _ _ k

example : Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) 1)
    (NerveBoundaryExtension.extend F faces hf old hfaces hcof hfib hp) =
      NerveParameterExtension.familyVertices F old :=
  NerveBoundaryExtension.extend_restrict F faces hf old hfaces hcof hfib hp
end GeneralHigherBoundaries

section ActualMixedTriangles
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)
open MixedChoiceCoherentIntervals MixedChoiceCoherentTriangles

-- Actual old triangles are retained at each context, without a supplied coherent boundary input.
example (left : Bool) (t : MixedChoiceFunctor.Context Y W) :
    NerveParameterExtension.evaluate (values hcof Y W g) (triangle hcof hfib Y W g left) t =
      CoherentLiftMixedComparison.triangle hcof hfib t.1.unop.left.inner Y.inner W t.2.right
        t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) left :=
  triangle_evaluate _ _ _ _ _ left t

-- Every face is the already selected whole edge system, including the shared diagonal.
example (left : Bool) (k : Fin 3) : triangle hcof hfib Y W g left ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ k)) =
    interval hcof hfib Y W g (faceEdge left k) := triangle_face _ _ _ _ _ left k

example : triangle hcof hfib Y W g true ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (1 : Fin 3))) =
    triangle hcof hfib Y W g false ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (1 : Fin 3))) := shared_diagonal _ _ _ _ _

-- All external simplex operators act on one triangle family, including the changing endpoint.
example (left : Bool) {n m : ℕ} (c : ComposableArrows (MixedChoiceFunctor.Context Y W) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ (triangle hcof hfib Y W g left).app (ofChain c) =
    (triangle hcof hfib Y W g left).app
      (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (NerveParameterExtension.cotensor (values hcof Y W g) _).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveCoherentFamily.reindex_compatibility _ _ c θ
end ActualMixedTriangles

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBoundaryExtension,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedChoiceCoherentTriangles,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveIntervalBoundary,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedChoiceCoherentIntervals]
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
    throwError "Some coherent boundary modules were not audited"
  logInfo m!"Coherent higher boundary audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
