import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := SerrePositivity.Reedy.simplexModelCategory C

-- The original actual frame map is retained in the outer resolution morphism.
example {X Y : ResolutionObject C} (f : X ⟶ Y) (φ : ResolutionLiftPrecomposition.FrameMap f) :
    (FrameLiftSpace.outerMap f φ).diagram = φ.val := FrameLiftSpace.outerMap_diagram f φ

-- Inner equality changes the type of the point without changing the original frame composite.
example {A B D E : FramedResolution C} (s : A ⟶ B) (t : B ⟶ E) (u : A ⟶ D) (v : D ⟶ E)
    (h : (s ≫ t).map = (u ≫ v).map) :
    (FrameSquareComparison.rightFrame s t u v h).val = u.frame ≫ v.frame :=
  FrameSquareComparison.rightFrame_val s t u v h

variable (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

-- Comparison values stay in the original Hom universe despite the large bar index.
example {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) : SSet.{v} :=
  ResolutionBarFrameSquares.leftSpace R a f

example {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    (ResolutionBarFrameSquares.leftSourceMap R f ≫ ResolutionBarFrameSquares.leftCone R a t).map =
      (ResolutionBarFrameSquares.leftCone R a s ≫
        ResolutionBarFrameSquares.leftTargetMap R f).map :=
  ResolutionBarFrameSquares.left_inner_square R a f

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

example {X Y : ResolutionObject C} (f : X ⟶ Y) :
    trivialFibrations SSet.{v} (FrameLiftSpace.projection f) :=
  FrameLiftSpace.projection_trivialFibration f hcof

-- Both interval endpoints are the original actual composites over the same inner map.
example {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
        ResolutionBarFrameSquares.leftSpace R a f,
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ e =
          ResolutionBarFrameSquares.leftStart R a f ∧
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ e =
          ResolutionBarFrameSquares.leftFinish R a f :=
  ResolutionBarFrameSquares.left_interval R a hcof f

-- Arbitrary full boundary families extend simultaneously on both sides.
example {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i]
    (l : K ⟶ ResolutionBarFrameSquares.leftSpace R a f)
    (r : K ⟶ ResolutionBarFrameSquares.rightSpace R b f) :
    ∃ (l' : L ⟶ ResolutionBarFrameSquares.leftSpace R a f)
      (r' : L ⟶ ResolutionBarFrameSquares.rightSpace R b f), i ≫ l' = l ∧ i ≫ r' = r :=
  ResolutionBarFrameSquares.pair_extension R a b hcof f i l r

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameLiftSpace,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameSquareComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares]
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
    throwError "Some resolution bar frame square modules were not audited"
  logInfo m!"Resolution bar frame square audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
