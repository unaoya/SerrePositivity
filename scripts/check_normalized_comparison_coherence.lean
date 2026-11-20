import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedComparisonSquare
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarUnitCoherence
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel KanComparisonTriangle

section Tetrahedron
variable {T U K : SSet.{v}} {f g h z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h z)
  (a : Data F G) (b : Data F H) (c : Data G H)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (i : U ⟶ T)

example : SSet.stdSimplex.δ (0 : Fin 4) ≫
    (NormalizedComparisonTetrahedron.build F G H a b c hK).tetrahedron = c.triangle :=
  (NormalizedComparisonTetrahedron.build F G H a b c hK).face_zero
example : uncurry (NormalizedComparisonTetrahedron.tetrahedron
    (HomotopyClasses.preHomotopy i F) (HomotopyClasses.preHomotopy i G)
    (HomotopyClasses.preHomotopy i H)
    (ComparisonCoherenceRestriction.triangle i F G a)
    (ComparisonCoherenceRestriction.triangle i F H b)
    (ComparisonCoherenceRestriction.triangle i G H c) hK) =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫
        uncurry (NormalizedComparisonTetrahedron.tetrahedron F G H a b c hK) :=
  NormalizedComparisonTetrahedron.family_reindex F G H a b c hK i
example (d : KanComparisonTetrahedron.Filler F G H a b c) :
    RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn 3 3).ι
      (KanComparisonTetrahedron.hornMap F G H a b c) d.tetrahedron
      (NormalizedComparisonTetrahedron.tetrahedron F G H a b c hK) :=
  NormalizedComparisonTetrahedron.compare F G H a b c hK d
end Tetrahedron

section Disc
variable {T U K : SSet.{v}} {f₀ f₁ f₂ f₃ z : T ⟶ K}
  (F₀ : SSet.Homotopy f₀ z) (F₁ : SSet.Homotopy f₁ z)
  (F₂ : SSet.Homotopy f₂ z) (F₃ : SSet.Homotopy f₃ z)
  (a : Data F₀ F₁) (b : Data F₁ F₂) (c : Data F₀ F₃) (d : Data F₃ F₂)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (i : U ⟶ T)
local notation "G₀" => HomotopyClasses.preHomotopy i F₀
local notation "G₁" => HomotopyClasses.preHomotopy i F₁
local notation "G₂" => HomotopyClasses.preHomotopy i F₂
local notation "G₃" => HomotopyClasses.preHomotopy i F₃
local notation "ta" => ComparisonCoherenceRestriction.triangle i F₀ F₁ a
local notation "tb" => ComparisonCoherenceRestriction.triangle i F₁ F₂ b
local notation "tc" => ComparisonCoherenceRestriction.triangle i F₀ F₃ c
local notation "td" => ComparisonCoherenceRestriction.triangle i F₃ F₂ d

example : (NormalizedComparisonSquare.build G₀ G₁ G₂ G₃ ta tb tc td hK).left.tetrahedron =
    (NormalizedComparisonSquare.build F₀ F₁ F₂ F₃ a b c d hK).left.tetrahedron ≫ (pre i).app K :=
  NormalizedComparisonSquare.left_tetrahedron_reindex F₀ F₁ F₂ F₃ a b c d hK i
example : NormalizedComparisonSquare.left G₀ G₁ G₂ G₃ ta tb tc td hK =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
      NormalizedComparisonSquare.left F₀ F₁ F₂ F₃ a b c d hK :=
  NormalizedComparisonSquare.left_reindex F₀ F₁ F₂ F₃ a b c d hK i
example : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    NormalizedComparisonSquare.left F₀ F₁ F₂ F₃ a b c d hK =
    T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
      NormalizedComparisonSquare.right F₀ F₁ F₂ F₃ a b c d hK :=
  NormalizedComparisonSquare.common_diagonal F₀ F₁ F₂ F₃ a b c d hK
end Disc

section Native
open SerrePositivity.HomotopyFunctionComplex
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (cX : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X X)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
local notation "F" => OrdinaryBarUnitTriangles.root hcof hfib P j f c
local notation "G" => OrdinaryBarUnitTriangles.leftIntermediate hcof hfib P j f cX c
local notation "a" => OrdinaryBarUnitTriangles.leftOutgoing hcof hfib P j f cX c
local notation "b" => ComparisonTriangleDegeneracy.diagonal F
local notation "d" => OrdinaryBarUnitTriangles.leftReturn hcof hfib P j f cX c
local notation "e" => OrdinaryBarUnitCoherence.leftData hcof hfib P j f cX c
local notation "hK" => SimplexParameterHom.native_kan (small hcof hfib X) (small hcof hfib Y)
  (OrdinaryBarSmallReference.value_kan hcof hfib Y)

-- The old actual native unit tetrahedron is compared with all three whole faces fixed.
example : RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn 3 3).ι
    (KanComparisonTetrahedron.hornMap F G F a b d) (e).tetrahedron
    (NormalizedComparisonTetrahedron.tetrahedron F G F a b d hK) :=
  NormalizedComparisonTetrahedron.compare F G F a b d hK e
example : SSet.stdSimplex.δ (2 : Fin 4) ≫
    (NormalizedComparisonTetrahedron.build F G F a b d hK).tetrahedron =
      (compositionTriangle hcof hfib P j (OrdinaryBarUnitTriangles.identityWord (T := T) X)
        f cX c c).triangle :=
  (NormalizedComparisonTetrahedron.build F G F a b d hK).face_two
end Native

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedComparisonTetrahedron,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedComparisonSquare]
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
  unless modules.size == expected.size do throwError "Missing normalized coherence modules"
  logInfo m!"Normalized coherence audit passed: {count} declarations in {modules.size} modules."
