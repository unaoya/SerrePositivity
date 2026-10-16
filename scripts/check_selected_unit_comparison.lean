import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

-- This is the actual standard degeneracy, with its exact two vertices.
example {P : SSet.{v}} (a : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ P) (j : Fin 2) :
    SSet.stdSimplex.δ j ≫ SelectedLoopContraction.degenerate a = a :=
  SelectedLoopContraction.degenerate_vertex a j

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)

example (post : Bool) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ CoherentLiftUnitComparison.loop hcof hfib X Y f post =
        chosenPoint hcof X Y f ∧
      SSet.stdSimplex.δ (0 : Fin 2) ≫ CoherentLiftUnitComparison.loop hcof hfib X Y f post =
        chosenPoint hcof X Y f :=
  ⟨CoherentLiftUnitComparison.loop_zero hcof hfib X Y f post,
    CoherentLiftUnitComparison.loop_one hcof hfib X Y f post⟩

-- The selected loop is kept; the other two faces are literal standard degeneracies.
example (post : Bool) :
    SSet.stdSimplex.δ (0 : Fin 3) ≫ CoherentLiftUnitComparison.triangle hcof hfib X Y f post =
        SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) ≫ chosenPoint hcof X Y f ∧
      SSet.stdSimplex.δ (1 : Fin 3) ≫ CoherentLiftUnitComparison.triangle hcof hfib X Y f post =
        SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) ≫ chosenPoint hcof X Y f ∧
      SSet.stdSimplex.δ (2 : Fin 3) ≫ CoherentLiftUnitComparison.triangle hcof hfib X Y f post =
        CoherentLiftUnitComparison.loop hcof hfib X Y f post :=
  ⟨CoherentLiftUnitComparison.triangle_face hcof hfib X Y f post 0,
    CoherentLiftUnitComparison.triangle_face hcof hfib X Y f post 1,
    CoherentLiftUnitComparison.triangle_face hcof hfib X Y f post 2⟩

-- In particular this contracts the original chosen identity comparison, after
-- its base transport, not a freshly chosen null loop.
example : SSet.stdSimplex.δ (2 : Fin 3) ≫ CoherentLiftUnitComparison.triangle hcof hfib X Y f true =
    postEdge hcof hfib X Y Y f (𝟙 Y) ≫ CoherentLiftUnitComparison.postComparisonMap hcof X Y f :=
  CoherentLiftUnitComparison.triangle_face hcof hfib X Y f true 2

example : SSet.stdSimplex.δ (2 : Fin 3) ≫
    CoherentLiftUnitComparison.triangle hcof hfib X Y f false =
    preEdge hcof hfib X X Y (𝟙 X) f (ResolutionLiftPrecomposition.identity X) ≫
      CoherentLiftUnitComparison.preComparisonMap hcof X Y f :=
  CoherentLiftUnitComparison.triangle_face hcof hfib X Y f false 2

example (post : Bool) : vertexInclusion X Y f ▷
        SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family (vertexInclusion X Y f) (vertexData X Y f)
          (CoherentLiftUnitComparison.triangle hcof hfib X Y f post) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ vertexData X Y f :=
  CoherentLiftUnitComparison.triangle_fixed_boundary hcof hfib X Y f post

-- The same contraction acts into the existing Kan targets for every Z and t.
example (post : Bool) (Z : C) (t : CoherentLiftTuples.obj X Y f ⊗
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ (cosimplicialHom Y.resolution.obj).obj Z)
    (k : Fin 3) :
    CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k ≫
        KanLiftAction.parameterized hcof hfib X Y f Z
          (RelativeChoiceSpace.family (vertexInclusion X Y f) (vertexData X Y f)
            (CoherentLiftUnitComparison.triangle hcof hfib X Y f post)) t =
      KanLiftAction.parameterized hcof hfib X Y f Z
        (RelativeChoiceSpace.family (vertexInclusion X Y f) (vertexData X Y f)
          ((CoherentLiftUnitComparison.data hcof hfib X Y f post).faces k))
        ((CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k) ≫ t) :=
  CoherentLiftUnitComparison.triangle_action_face hcof hfib X Y f post Z t k

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SelectedLoopContraction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison]
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
  unless modules.size == expected.size do throwError "Some selected unit modules were not audited"
  logInfo m!"Selected unit comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
