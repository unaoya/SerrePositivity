import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Quillen SerrePositivity.Reedy

variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- The general comparison permits a merely weak augmentation on one side;
-- there is no hidden Reedy trivial-fibration hypothesis on p.
example
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (q : CofibrantResolutionFamily (C := C) simplex) (p : CosimplicialFrameFamily (C := C))
    (X : C) (n : SimplexCategory) :
    weakEquivalences C (((FrameComparison.left cof q p).app X).app n) ∧
      weakEquivalences C (((FrameComparison.right cof q p).app X).app n) :=
  ⟨FrameComparison.left_weakEquivalence cof q p X n,
    FrameComparison.right_weakEquivalence cof q p X n⟩

variable [EnrichedOrdinaryCategory SSet.{v} C] [ModelCategory SSet.{v}]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C) [IsQuillenBifunctor S.tensor]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{v} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

-- Final input consists of the existing tensor/SM7 and two explicit source
-- factorizations. No Q, R, frame, or comparison weak equivalence is assumed.
example (X : Cᵒᵖ) (Y : C) :
    SerrePositivity.SimplicialHomotopy.weakEquivalences
        (((ChosenMapComparison.fromResolution S hcof hw cof fib).app X).app Y) ∧
      SerrePositivity.SimplicialHomotopy.weakEquivalences
        (((ChosenMapComparison.fromMap S hcof hw cof fib).app X).app Y) :=
  ChosenMapComparison.geometricWeakEquivalences S hcof hw cof fib X Y

example (X : Cᵒᵖ) (Y : C) :
    SSet.KanComplex (((ChosenMapComparison.middle S hcof hw cof fib).obj X).obj Y) :=
  ChosenMapComparison.middle_kanComplex S hcof hw cof fib X Y

-- The endpoint is literally the actual enriched Map, in every simplicial
-- degree, rather than an opaque stand-in for a derived mapping object.
example (X : Cᵒᵖ) (Y : C) :
    ((enrichedReplacementHom (cofibrantSource cof) (fibrantTarget fib)).obj X).obj Y =
      ((cofibrantSource cof).obj X.unop ⟶[SSet.{v}] (fibrantTarget fib).obj Y) := rfl

-- Naturality in the target and source are equalities of actual SSet maps.
example (X : Cᵒᵖ) {Y Y' : C} (g : Y ⟶ Y') :
    ((enrichedReplacementHom (cofibrantSource cof) (fibrantTarget fib)).obj X).map g ≫
        ((ChosenMapComparison.fromMap S hcof hw cof fib).app X).app Y' =
      ((ChosenMapComparison.fromMap S hcof hw cof fib).app X).app Y ≫
        ((ChosenMapComparison.middle S hcof hw cof fib).obj X).map g :=
  ((ChosenMapComparison.fromMap S hcof hw cof fib).app X).naturality g

example {X X' : Cᵒᵖ} (f : X ⟶ X') :
    (enrichedReplacementHom (cofibrantSource cof) (fibrantTarget fib)).map f ≫
        (ChosenMapComparison.fromMap S hcof hw cof fib).app X' =
      (ChosenMapComparison.fromMap S hcof hw cof fib).app X ≫
        (ChosenMapComparison.middle S hcof hw cof fib).map f :=
  (ChosenMapComparison.fromMap S hcof hw cof fib).naturality f

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialFrameFamily,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialMapComparison,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Simplicial Map comparison audit passed: {count} declarations in {seen.size} modules."
