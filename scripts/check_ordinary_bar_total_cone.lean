import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v uC vC uD vD w uH vH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

-- Both object universes and Hom universes are independent.
example {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F G : C ⥤ D} (α : F ⟶ G) :
    SSet.Homotopy (SerrePositivity.NerveHomotopyUniverse.map F)
      (SerrePositivity.NerveHomotopyUniverse.map G) :=
  SerrePositivity.NerveHomotopyUniverse.homotopy α

-- A known lift has an actual simplex-category equivalence; arbitrary bars are not shrunk.
example (X : SSet.{v}) : X.Elements ≌ (UniverseLift.obj.{w} X).Elements :=
  UniverseLift.elementsEquivalence X

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

-- The one natural transformation records the original labels and varying degrees.
example : OrdinaryBarTotalCone.first R ⟶ OrdinaryBarTotalCone.rows R a b :=
  OrdinaryBarTotalCone.cone R a b

example (s : OrdinaryBarTotalCone.Index R) :
    ((OrdinaryBarTotalCone.cone R a b).app s).hom.2 = 𝟙 s.obj :=
  OrdinaryBarTotalCone.cone_degree R a b s

example {s t : OrdinaryBarTotalCone.Index R} (f : s ⟶ t) :
    (OrdinaryBarTotalCone.first R).map f ≫ (OrdinaryBarTotalCone.cone R a b).app t =
      (OrdinaryBarTotalCone.cone R a b).app s ≫ (OrdinaryBarTotalCone.rows R a b).map f :=
  (OrdinaryBarTotalCone.cone R a b).naturality f

example (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ((OrdinaryBarTotalCone.rows R a b).obj
      ((OrdinaryBarEvaluation.bar R).elementsMk n c)).val =
      ((OrdinaryBarEvaluation.evaluation R a b).app n c).down :=
  OrdinaryBarTotalCone.row_label R a b n c

-- This is a factorization of whole functors, including every actual simplex operator.
example : OrdinaryBarTotalCone.rows R a b ≅
    OrdinaryBarTotalEvaluation.evaluationElements R a b ⋙
      OrdinaryBarTotalEvaluation.rowElements R :=
  OrdinaryBarTotalEvaluation.rowFactorization R a b

example : OrdinaryBarTotalCone.first R ⟶
    OrdinaryBarTotalEvaluation.evaluationElements R a b ⋙
      OrdinaryBarTotalEvaluation.rowElements R :=
  OrdinaryBarTotalEvaluation.comparison R a b

example : SSet.Homotopy (OrdinaryBarTotalHomotopy.firstMap R)
    (OrdinaryBarTotalHomotopy.evaluatedMap R a b) :=
  OrdinaryBarTotalHomotopy.homotopy R a b

-- No model in the auxiliary universe, and no extra structure on C, is assumed.
example {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.map (OrdinaryBarTotalHomotopy.firstMap R) =
      L.map (OrdinaryBarTotalHomotopy.evaluatedMap R a b) :=
  OrdinaryBarTotalHomotopy.image_eq R a b L hL

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.ElementsNaturalPrecomp,
    `SerrePositivity.CategoryTheory.NerveHomotopyUniverse,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftElements,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy]
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
  unless modules.size == expected.size do throwError "Missing total cone modules"
  logInfo m!"Ordinary bar total cone audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
