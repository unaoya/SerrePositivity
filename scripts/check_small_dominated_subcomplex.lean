import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v w uD vD
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- General domination, with independent value and smallness universes, needs no model.
example {X K : SSet.{w}} (s : K ⟶ X) (q : X ⟶ K)
    (H : SSet.Homotopy (𝟙 X) (q ≫ s)) (A : X.Subcomplex)
    (hK : ∀ n, Small.{v} (K.obj n)) (hA : SmallParameterClosure.IsSmall.{v} A) :
    SmallParameterClosure.IsSmall.{v} (SmallDominatedSubcomplex.complex s q H A) :=
  SmallDominatedSubcomplex.small s q H A hK hA

example {X K : SSet.{w}} (s : K ⟶ X) (q : X ⟶ K)
    (H : SSet.Homotopy (𝟙 X) (q ≫ s)) (A : X.Subcomplex) :
    A ≤ SmallDominatedSubcomplex.complex s q H A :=
  SmallDominatedSubcomplex.seed_le s q H A

example {X K : SSet.{w}} (s : K ⟶ X) (q : X ⟶ K)
    (H : SSet.Homotopy (𝟙 X) (q ≫ s)) (A : X.Subcomplex) :
    SSet.Homotopy (𝟙 (SmallDominatedSubcomplex.complex s q H A).toSSet)
      ((SmallDominatedSubcomplex.complex s q H A).ι ≫
        SmallDominatedSubcomplex.retraction s q H A) :=
  SmallDominatedSubcomplex.restrictedHomotopy s q H A

-- Already-small degrees may be shrunk simultaneously over a large base category.
example {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{max w v})
    (hF : ∀ d n, Small.{v} ((F.obj d).obj n)) :
    SmallSimplicialValue.shrinkDiagram F hF ⋙ SSet.uliftFunctor.{max w v, v} ≅ F :=
  SmallSimplicialValue.diagramLiftIso F hF

variable {C : Type w} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X : Cᵒᵖ × C) (A : (OrdinaryBarSmallSubcomplex.ambient X).Subcomplex)
  (hA : SmallParameterClosure.IsSmall.{v} A)

-- The old comparison extends exactly along the actual large horn-replacement unit.
example : AnodyneKanReplacement.unit.app (OrdinaryResolutionBar.functor.obj X) ≫
    OrdinaryBarSmallSubcomplex.toSmall hcof hfib X =
      OrdinaryBarSmallReference.toReference hcof hfib X :=
  OrdinaryBarSmallSubcomplex.unit_toSmall hcof hfib X

example : A ≤ OrdinaryBarSmallSubcomplex.complex hcof hfib X A :=
  OrdinaryBarSmallSubcomplex.seed_le hcof hfib X A

-- This is an actual small simplicial object, not merely a homotopy-class type.
example : SSet.{v} := OrdinaryBarSmallSubcomplex.smallValue hcof hfib X A hA

example : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarSmallSubcomplex.smallInclusion hcof hfib X A hA)) :=
  OrdinaryBarSmallSubcomplex.smallInclusion_isIso hcof hfib X A hA

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SmallActionClosure,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SmallDominatedSubcomplex,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SmallSimplicialValue,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex]
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
    throwError "Missing small dominated subcomplex modules"
  logInfo m!"Small dominated subcomplex audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
