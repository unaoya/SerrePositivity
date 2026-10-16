import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

-- All simplicial values may be in the auxiliary universe; no model there is required.
variable {A B C P K X E : SSet.{max u v}}
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

-- Equality in the generated quotient supplies one actual interval into the original K.
example {f g : X ⟶ K} (h : HomotopyClasses.mk f = HomotopyClasses.mk g) :
    Nonempty (SSet.Homotopy f g) := KanActualHomotopy.of_class_eq hK h

example {f g h : X ⟶ K} (Hfg : SSet.Homotopy f g) (Hgh : SSet.Homotopy g h) :
    Nonempty (SSet.Homotopy f h) := KanActualHomotopy.concatenate hK Hfg Hgh

-- This equivalence needs neither target Kan nor a model structure.
example : HomotopyClasses.obj (B ⊗ X) K ≃ HomotopyClasses.obj X ((ihom B).obj K) :=
  HomotopyClassesClosed.equiv

-- Localized equivalence, rather than a preselected actual contraction, is sufficient.
example (p : E ⟶ K) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map p)) :
    (MorphismProperty.monomorphisms SSet.{max u v}).rlp p :=
  KanFibrationLocalizedLifting.of_localized_isIso p hp hK hf

variable (i : A ⟶ B) [Mono i] (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))

example : (MorphismProperty.monomorphisms SSet.{max u v}).rlp
    ((MonoidalClosed.pre i).app K) := KanRestrictionLifting.all_mono_rlp i hi hK

-- Both original endpoints and the complete specified restricted homotopy are retained.
example (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    ∃ V : SSet.Homotopy f g,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h :=
  KanMonoRelativeHomotopy.exists_extension i hi hK f g H

variable (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)

-- j is arbitrary. No cofinality, split projection, or enlarged model is supplied.
example (f f' : P ⟶ K) (H : SSet.Homotopy (g ≫ f) (g ≫ f')) :
    ∃ V : SSet.Homotopy f f',
      g ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h :=
  KanMonoPushoutEquivalence.exists_homotopy i j u g sq hi hK f f' H

example : Function.Bijective (HomotopyClasses.pre g (K := K)) :=
  KanMonoPushoutEquivalence.tests i j u g sq hi K hK

example : IsIso (AnodyneHomotopy.anodyneQ.map g) :=
  KanMonoPushoutEquivalence.localized_isIso i j u g sq hi

example {D : Type uH} [Category.{vH} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map g) :=
  KanMonoPushoutEquivalence.image_isIso i j u g sq hi L hL

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClassesClosed,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionLifting,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence]
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
  unless modules.size == expected.size do throwError "Missing Kan pushout equivalence modules"
  logInfo m!"Kan pushout equivalence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
