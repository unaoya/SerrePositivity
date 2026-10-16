import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v uI vI uB vB uH vH u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- Arbitrary index maps; neither cofinality nor a larger simplicial model is an input.
example {E D : Type uI} [Category.{vI} E] [Category.{vI} D]
    {B : Type uB} [Category.{vB} B] (q : E ⥤ D) (p : D ⥤ B) (F : D ⥤ SSet.{v})
    {H : Type uH} [Category.{vH} H] (L : SSet.{max uI vI v vB} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    BarConstruction.spanMiddle (q ⋙ p) (q ⋙ F) ⋙ L ≅
      (q ⋙ BarConstruction.spanMiddle p F) ⋙ L :=
  BarConstruction.middleReindexImageIso q p F L hL

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

example : OrdinaryResolutionBar.middleComparison (C := C) ≫
    Functor.whiskerLeft OrdinaryResolutionPairs.forgetFrames
      OrdinaryResolutionBar.ordinaryRight = OrdinaryResolutionBar.right :=
  OrdinaryResolutionBar.right_factorization

example : IsIso (Functor.whiskerRight (OrdinaryResolutionBar.right (C := C)) L) ↔
    IsIso (Functor.whiskerRight (OrdinaryResolutionBar.ordinaryRight (C := C)) L) :=
  OrdinaryResolutionBar.right_natural_image_isIso_iff L hL

-- The canonical model-free localization is one actual consumer of the reduction.
example :
    IsIso (Functor.whiskerRight (OrdinaryResolutionBar.right (C := C))
      AnodyneHomotopy.anodyneQ) ↔
    IsIso (Functor.whiskerRight (OrdinaryResolutionBar.ordinaryRight (C := C))
      AnodyneHomotopy.anodyneQ) :=
  OrdinaryResolutionBar.right_natural_image_isIso_iff AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction]
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
  unless modules.size == expected.size do throwError "Missing reduction modules"
  logInfo m!"Ordinary bar reduction audit passed: {count} declarations in {modules.size} modules."
