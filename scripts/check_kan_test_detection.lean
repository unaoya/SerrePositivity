import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

-- The actual horn construction supplies the data, not an assumed simplicial model.
example (X : SSet.{v}) :
    SSet.anodyneExtensions (AnodyneKanReplacement.unit.app X) :=
  AnodyneKanReplacement.unit_anodyne X

example (X : SSet.{v}) : SSet.modelCategoryQuillen.J.rlp
    (terminal.from (AnodyneKanReplacement.functor.obj X)) :=
  AnodyneKanReplacement.terminal_rlp X

example {X Y : SSet.{v}} (f : X ⟶ Y) :
    f ≫ AnodyneKanReplacement.unit.app Y =
      AnodyneKanReplacement.unit.app X ≫ AnodyneKanReplacement.functor.map f :=
  AnodyneKanReplacement.unit.naturality f

-- All target tests are Kan tests; no replacement of the prescribed weak class is assumed.
example {X Y : SSet.{v}} (f : X ⟶ Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map f) ↔ KanTestDetection.Tests f :=
  KanTestDetection.anodyneQ_isIso_iff_tests f

example {X Y : SSet.{v}} (f : X ⟶ Y) (hf : KanTestDetection.Tests f)
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map f) :=
  KanTestDetection.map_isIso_of_tests f L hL hf

-- Arbitrary enlarged value universe, with the same actual tensor maps and no model there.
example {X Y : SSet.{max u v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) (A : SSet.{max u v}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (A ◁ f)) :=
  AnodyneHomotopy.whiskerLeft_anodyneQ_isIso f hf A

example {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) (A : SSet.{v})
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map (f ▷ A)) :=
  AnodyneHomotopy.whiskerRight_image_isIso f hf A L hL

-- The previous standard-simplex theorem provides the actual starting Kan tests.
example (n : ℕ) : KanTestDetection.Tests (SimplexNerve.augmentation.app
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n))) :=
  KanTestDetection.tests_of_anodyneQ_isIso _
    (SimplexNerve.standardAugmentation_isIso AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) n)

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor]
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
  unless modules.size == expected.size do throwError "Missing Kan test detection modules"
  logInfo m!"Kan test detection audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
