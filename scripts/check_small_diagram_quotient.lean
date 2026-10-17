import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v w uD vD uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{max w v}}
  (R : DiagramQuotient.Congruence F)
  (hsmall : ∀ d n, Small.{v} (Quotient (R.rel d n)))
  (hboundary : ∀ d, SSet.modelCategoryQuillen.I.rlp ((DiagramQuotient.projection R).app d))

-- The full base category and all value universes are independent; neither value needs a model.
example : F ⟶ SmallDiagramQuotient.functor R hsmall ⋙ SSet.uliftFunctor.{max w v, v} :=
  SmallDiagramQuotient.projection R hsmall

example {H : Type uH} [Category.{vH} H] (L : SSet.{max w v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    F ⋙ L ≅ (SmallDiagramQuotient.functor R hsmall ⋙ SSet.uliftFunctor.{max w v, v}) ⋙ L :=
  SmallDiagramQuotient.imageIso R hsmall hboundary L hL

include hboundary in
example (d : D) (hF : SSet.modelCategoryQuillen.J.rlp (terminal.from (F.obj d))) :
    SSet.modelCategoryQuillen.J.rlp
      (terminal.from ((SmallDiagramQuotient.functor R hsmall).obj d)) :=
  SmallDiagramQuotient.kan R hsmall hboundary d hF

-- Only weak equivalence detection in the original small model uses a ModelCategory input.
example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {d e : D} (f : d ⟶ e) (hf : IsIso (AnodyneHomotopy.anodyneQ.map (F.map f))) :
    weakEquivalences SSet.{v} ((SmallDiagramQuotient.functor R hsmall).map f) :=
  SmallDiagramQuotient.map_weakEquivalence R hsmall hboundary hcof hfib f hf

-- All certificates are proved for the earlier obstruction, with no models in either universe.
example : SmallSubdiagramObstruction.Index (Type v) ⥤ SSet.{v} :=
  StarDiagramSmallQuotient.functor

example : IsIso (Functor.whiskerRight StarDiagramSmallQuotient.projection.{v}
    AnodyneHomotopy.anodyneQ) :=
  (StarDiagramSmallQuotient.imageIso AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)).isIso_hom

example (d : SmallSubdiagramObstruction.Index (Type v)) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (StarDiagramSmallQuotient.functor.obj d)) :=
  StarDiagramSmallQuotient.kan d

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagramQuotient,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SmallDiagramQuotient,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.StarDiagramSmallQuotient]
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
    throwError "Missing small diagram quotient modules"
  logInfo m!"Small diagram quotient audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
