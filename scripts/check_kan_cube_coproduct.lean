import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w u v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.SimplicialModel

-- Independent value universe; no model structure and no Kan objects are supplied.
variable {A B C P A' B' C' P' : SSet.{max u v}}
  (i : A ⟶ B) (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
  (i' : A' ⟶ B') (j' : A' ⟶ C') (u' : B' ⟶ P') (g' : C' ⟶ P')
  (sq' : IsPushout i' j' u' g') [Mono i] [Mono i']
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (m : P ⟶ P')
  (hab : i ≫ b = a ≫ i') (hac : j ≫ c = a ≫ j')
  (hbm : u ≫ m = b ≫ u') (hcm : g ≫ m = c ≫ g')
  (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
  (hb : IsIso (AnodyneHomotopy.anodyneQ.map b))
  (hc : IsIso (AnodyneHomotopy.anodyneQ.map c))


include sq sq' hab hac hbm hcm ha hb hc in
example : IsIso (AnodyneHomotopy.anodyneQ.map m) :=
  KanPushoutCube.localized_isIso i j u g sq i' j' u' g' sq' a b c m hab hac hbm hcm ha hb hc

include sq sq' hab hac hbm hcm ha hb hc in
example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map m) :=
  KanPushoutCube.image_isIso i j u g sq i' j' u' g' sq' a b c m hab hac hbm hcm ha hb hc L hL

-- The family and value universes are independent; comparisons need not be mono.
example (I : Type w) [Small.{max u v} I] {X Y : I → SSet.{max u v}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (f i))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map f)) :=
  KanLocalizedCoproducts.localized_isIso I f hf

-- Arbitrary actual coproduct cocones and their prescribed comparison.
example (I : Type w) [Small.{max u v} I] {X Y : I → SSet.{max u v}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (f i)))
    (c : Cofan X) (d : Cofan Y) (hc : IsColimit c) (hd : IsColimit d)
    (t : c.pt ⟶ d.pt) (ht : ∀ i, c.inj i ≫ t = f i ≫ d.inj i) :
    IsIso (AnodyneHomotopy.anodyneQ.map t) :=
  KanLocalizedCoproducts.actual_localized_isIso I f hf c d hc hd t ht

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanPushoutCube,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts]
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
  unless modules.size == expected.size do throwError "Missing Kan cube and coproduct modules"
  logInfo m!"Kan cube and coproduct audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
