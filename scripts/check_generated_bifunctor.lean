import SerrePositivity.HomotopicalAlgebra.Foundations
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe w₁ w₂ u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.ModelGeneration
variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [ModelCategory C₁] [ModelCategory C₂] [ModelCategory C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} {H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁}
  (adj : F ⊣₂ G) (adjFlip : F.flip ⊣₂ H)
  (I₁ J₁ : MorphismProperty C₁) (I₂ J₂ : MorphismProperty C₂)
  [CofibrantlyGenerated.{w₁} I₁ J₁] [CofibrantlyGenerated.{w₂} I₂ J₂]
  (hII : ∀ {A B : C₁} (i : A ⟶ B), I₁ i →
    ∀ {X Y : C₂} (j : X ⟶ Y), I₂ j → ∀ sq : F.PushoutObjObj i j, Cofibration sq.ι)
  (hJI : ∀ {A B : C₁} (i : A ⟶ B), J₁ i →
    ∀ {X Y : C₂} (j : X ⟶ Y), I₂ j → ∀ sq : F.PushoutObjObj i j,
      trivialCofibrations C₃ sq.ι)
  (hIJ : ∀ {A B : C₁} (i : A ⟶ B), I₁ i →
    ∀ {X Y : C₂} (j : X ⟶ Y), J₂ j → ∀ sq : F.PushoutObjObj i j,
      trivialCofibrations C₃ sq.ι)

-- Independent categories and small-object universes; only generator tests
-- are input, with neither full Quillen compatibility nor target generation.
example : IsQuillenBifunctor F :=
  isQuillenBifunctor_of_generators adj adjFlip I₁ J₁ I₂ J₂ hII hJI hIJ

example : HasQuillenPullbackHom G := by
  have h := isQuillenBifunctor_of_generators adj adjFlip I₁ J₁ I₂ J₂ hII hJI hIJ
  exact (isQuillenBifunctor_iff_pullbackHom adj).1 h

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`SerrePositivity.CategoryTheory.LiftingProperties.ParametrizedGeneration,
        `SerrePositivity.HomotopicalAlgebra.Monoidal.GeneratedBifunctor].contains
        env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No generator bifunctor declarations audited"
  logInfo m!"Generated bifunctor audit passed: {count} declarations, standard axioms only."
