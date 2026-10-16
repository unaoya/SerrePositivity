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
  (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (h : W ⟶ V)

-- The actual boundary compatibility is constructed, even when the outer
-- frame map is itself constructed from the ordinary source model.
example (left : Bool) : BoundaryGluing.StandardCompatible
    (CoherentLiftMixedComparison.data hcof hfib X Y W V f g h
      (ResolutionLiftPrecomposition.lift f) left).faces :=
  SelectedTriangle.Boundary.compatible _

variable (φ : ResolutionLiftPrecomposition.FrameMap f)

-- All four outer faces are the original selected comparison edges, after
-- their actual transports. The two triangles do not reselect those edges.
example :
    SSet.stdSimplex.δ (0 : Fin 3) ≫
        CoherentLiftMixedComparison.triangle hcof hfib X Y W V f g h φ true =
          CoherentLiftMixedComparison.edgeBD hcof hfib X Y W V f g h φ ∧
      SSet.stdSimplex.δ (2 : Fin 3) ≫
        CoherentLiftMixedComparison.triangle hcof hfib X Y W V f g h φ true =
          CoherentLiftMixedComparison.edgeAB hcof hfib X Y W V f g h φ ∧
      SSet.stdSimplex.δ (0 : Fin 3) ≫
        CoherentLiftMixedComparison.triangle hcof hfib X Y W V f g h φ false =
          CoherentLiftMixedComparison.edgeCD hcof hfib X Y W V f g h φ ∧
      SSet.stdSimplex.δ (2 : Fin 3) ≫
        CoherentLiftMixedComparison.triangle hcof hfib X Y W V f g h φ false =
          CoherentLiftMixedComparison.edgeAC hcof hfib X Y W V f g h φ :=
  ⟨CoherentLiftMixedComparison.triangle_face hcof hfib X Y W V f g h φ true 0,
    CoherentLiftMixedComparison.triangle_face hcof hfib X Y W V f g h φ true 2,
    CoherentLiftMixedComparison.triangle_face hcof hfib X Y W V f g h φ false 0,
    CoherentLiftMixedComparison.triangle_face hcof hfib X Y W V f g h φ false 2⟩

-- Their shared diagonal agrees as an actual simplicial map.
example : SSet.stdSimplex.δ (1 : Fin 3) ≫
        CoherentLiftMixedComparison.triangle hcof hfib X Y W V f g h φ true =
      SSet.stdSimplex.δ (1 : Fin 3) ≫
        CoherentLiftMixedComparison.triangle hcof hfib X Y W V f g h φ false :=
  CoherentLiftMixedComparison.shared_diagonal hcof hfib X Y W V f g h φ

example (left : Bool) :
    vertexInclusion Y W g ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family (vertexInclusion Y W g)
          (CoherentLiftMixedComparison.boundary X Y W V f g h φ)
          (CoherentLiftMixedComparison.triangle hcof hfib X Y W V f g h φ left) =
      vertices Y W g ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          CoherentLiftMixedComparison.boundary X Y W V f g h φ :=
  CoherentLiftMixedComparison.triangle_fixed_boundary hcof hfib X Y W V f g h φ left

-- A single pair of triangles works in all targets, without source enrichment,
-- specified source functorial factorization, or target fibrancy.
example (left : Bool) (Z : C) (t : CoherentLiftTuples.obj Y W g ⊗
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ (cosimplicialHom V.resolution.obj).obj Z)
    (k : Fin 3) :
    CoherentLiftTuples.obj Y W g ◁ SSet.stdSimplex.δ k ≫
        KanLiftAction.parameterized hcof hfib X V (f.base ≫ g ≫ h.base) Z
          (RelativeChoiceSpace.family (vertexInclusion Y W g)
            (CoherentLiftMixedComparison.boundary X Y W V f g h φ)
            (CoherentLiftMixedComparison.triangle hcof hfib X Y W V f g h φ left)) t =
      KanLiftAction.parameterized hcof hfib X V (f.base ≫ g ≫ h.base) Z
        (RelativeChoiceSpace.family (vertexInclusion Y W g)
          (CoherentLiftMixedComparison.boundary X Y W V f g h φ)
          ((CoherentLiftMixedComparison.data hcof hfib X Y W V f g h φ left).faces k))
        ((CoherentLiftTuples.obj Y W g ◁ SSet.stdSimplex.δ k) ≫ t) :=
  CoherentLiftMixedComparison.triangle_action_face hcof hfib X Y W V f g h φ left Z t k

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SelectedTriangle,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison]
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
    throwError "Some mixed comparison modules were not audited"
  logInfo m!"Selected mixed comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
