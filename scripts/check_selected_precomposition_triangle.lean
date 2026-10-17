import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
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
  (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y ⟶ W) (h : W.base ⟶ V.base)

-- The outer maps can be constructed from the ordinary source model alone.
-- The direct comparison uses their actual composite, not an assumed law
-- for the independently chosen lift of f≫g.
example : BoundaryGluing.StandardCompatible
    (CoherentLiftPreComposition.faces hcof hfib X Y W V f g h
      (ResolutionLiftPrecomposition.lift f) (ResolutionLiftPrecomposition.lift g)) :=
  CoherentLiftPreComposition.faces_compatible hcof hfib X Y W V f g h _ _

variable (φ : ResolutionLiftPrecomposition.FrameMap f) (ψ : ResolutionLiftPrecomposition.FrameMap g)

-- Every side is the selected comparison or its actual transport.
example :
    SSet.stdSimplex.δ (0 : Fin 3) ≫
        CoherentLiftPreComposition.triangle hcof hfib X Y W V f g h φ ψ =
        CoherentLiftPreComposition.secondEdge hcof hfib X Y W V f g h φ ∧
      SSet.stdSimplex.δ (1 : Fin 3) ≫
          CoherentLiftPreComposition.triangle hcof hfib X Y W V f g h φ ψ =
        preEdge hcof hfib X W V (f ≫ g) h (ResolutionLiftPrecomposition.compose φ ψ) ∧
      SSet.stdSimplex.δ (2 : Fin 3) ≫
          CoherentLiftPreComposition.triangle hcof hfib X Y W V f g h φ ψ =
        CoherentLiftPreComposition.firstEdge hcof hfib X Y W V f g h φ ψ :=
  ⟨CoherentLiftPreComposition.triangle_face hcof hfib X Y W V f g h φ ψ 0,
    CoherentLiftPreComposition.triangle_face hcof hfib X Y W V f g h φ ψ 1,
    CoherentLiftPreComposition.triangle_face hcof hfib X Y W V f g h φ ψ 2⟩

example : vertexInclusion W V h ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family (vertexInclusion W V h) (preBoundary X W V (f ≫ g) h)
          (CoherentLiftPreComposition.triangle hcof hfib X Y W V f g h φ ψ) =
      vertices W V h ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ preBoundary X W V (f ≫ g) h :=
  CoherentLiftPreComposition.triangle_fixed_boundary hcof hfib X Y W V f g h φ ψ

-- A single triangle acts with the prescribed side restrictions for every
-- Z and t; source enrichment, source FF, and fibrancy of Z are absent.
example (Z : C) (t : CoherentLiftTuples.obj W V h ⊗
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ (cosimplicialHom V.resolution.obj).obj Z)
    (k : Fin 3) :
    CoherentLiftTuples.obj W V h ◁ SSet.stdSimplex.δ k ≫
        KanLiftAction.parameterized hcof hfib X V ((f ≫ g).base ≫ h) Z
          (RelativeChoiceSpace.family (vertexInclusion W V h) (preBoundary X W V (f ≫ g) h)
            (CoherentLiftPreComposition.triangle hcof hfib X Y W V f g h φ ψ)) t =
      KanLiftAction.parameterized hcof hfib X V ((f ≫ g).base ≫ h) Z
        (RelativeChoiceSpace.family (vertexInclusion W V h) (preBoundary X W V (f ≫ g) h)
          (CoherentLiftPreComposition.faces hcof hfib X Y W V f g h φ ψ k))
        ((CoherentLiftTuples.obj W V h ◁ SSet.stdSimplex.δ k) ≫ t) :=
  CoherentLiftPreComposition.triangle_action_face hcof hfib X Y W V f g h φ ψ Z t k

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftFunctorLaws,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftPreComposition]
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
    throwError "Some selected pretriangle modules were not audited"
  logInfo m!"Selected precomposition triangle audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
