import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

-- Both degeneracies are preserved by the same chosen operation.
example (K : SSet.{v}) (i : Fin 3)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (d : Fin 2) :
    DegenerateHornInput.boundary i d K ≫ NormalizedTriangleHorn.section_ K i hK =
      DegenerateHornInput.degeneracy d K := NormalizedTriangleHorn.section_degeneracy K i hK d
example {T K : SSet.{v}} {f g z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) {U : SSet.{v}} (j : U ⟶ T) :
    NormalizedComparisonTriangle.triangle (HomotopyClasses.preHomotopy j F)
      (HomotopyClasses.preHomotopy j G) hK =
    NormalizedComparisonTriangle.triangle F G hK ≫ (pre j).app K :=
  NormalizedComparisonTriangle.triangle_reindex F G hK j
example {T K : SSet.{v}} {f z : T ⟶ K} (F : SSet.Homotopy f z)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    NormalizedComparisonTriangle.triangle F F hK =
      (ComparisonTriangleDegeneracy.diagonal F).triangle :=
  NormalizedComparisonTriangle.diagonal_triangle F hK
example {T K : SSet.{v}} {f z : T ⟶ K} (F : SSet.Homotopy f z)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    (KanComparisonTriangle.comparison F F (NormalizedComparisonTriangle.build F F hK)).h =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f :=
  NormalizedComparisonTriangle.diagonal_comparison F hK

open SerrePositivity.HomotopyFunctionComplex
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Z)

local notation "F" => nativeRestrictionComparison hcof hfib P j
  (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e
local notation "G" => compositionComparison hcof hfib P j f g c d
local notation "K" => CategoryTheory.Functor.obj (ihom (small hcof hfib X)) (small hcof hfib Z)
local notation "hK" => SimplexParameterHom.native_kan (small hcof hfib X) (small hcof hfib Z)
  (OrdinaryBarSmallReference.value_kan hcof hfib Z)

variable {U : SSet.{v}} (i : U ⟶ T)

-- Actual native inputs are re-evaluated at the new parameter, with independent u and v.
example : (normalizedCompositionTriangle hcof hfib P (UniverseLift.map i ≫ j)
    (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g)
    (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d) (UniverseLift.map i ≫ e)).triangle =
    (normalizedCompositionTriangle hcof hfib P j f g c d e).triangle ≫ (pre i).app K :=
  normalizedCompositionTriangle_reindex hcof hfib P j f g c d e i
example : (normalizedNativeCompositionComparison hcof hfib P (UniverseLift.map i ≫ j)
    (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g)
    (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d) (UniverseLift.map i ≫ e)).h =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
      (normalizedNativeCompositionComparison hcof hfib P j f g c d e).h :=
  normalizedNativeCompositionComparison_reindex hcof hfib P j f g c d e i
example : RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn 2 2).ι
    (KanComparisonTriangle.hornMap F G) (compositionTriangle hcof hfib P j f g c d e).triangle
    (normalizedCompositionTriangle hcof hfib P j f g c d e).triangle :=
  normalizeCompositionTriangleComparison hcof hfib P j f g c d e

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateTriangleOverlap,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedTriangleHorn,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NaturalHornFilling,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedComparisonTriangle,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle]
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
  unless modules.size == expected.size do throwError "Missing normalized native triangle modules"
  logInfo m!"Normalized triangle audit passed: {count} declarations in {modules.size} modules."
