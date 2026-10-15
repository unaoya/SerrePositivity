import SerrePositivity.HomotopicalAlgebra.Smith.WeakReflectionApproximation
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Smith

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

example {P : ObjectProperty C} [IsCardinalAccessibleCategory C κ]
    (h : LocalPresentableCover P κ) [HasCardinalFilteredColimits.{w} P.FullSubcategory κ]
    [P.ι.IsCardinalAccessible κ] : IsCardinalAccessibleCategory P.FullSubcategory κ :=
  h.isCardinalAccessibleCategory

example {P : ObjectProperty C} (r : PresentableWeakReflection P κ) :
    LocalPresentableCover P κ := r.localCover

example : LocalPresentableCover (⊤ : ObjectProperty C) κ where
  cover _ A _ f := ⟨A, inferInstance, trivial, 𝟙 A, f, Category.id_comp _⟩

example {D : Type u} [Category.{v} D] [IsCardinalAccessibleCategory C κ]
    (F : C ⥤ D) [F.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    {P : ObjectProperty D} (r : PresentableWeakReflection P κ)
    {X : C} (hX : P (F.obj X)) (A : C) [IsCardinalPresentable A κ] (f : A ⟶ X) :
    ∃ (B : C) (_ : IsCardinalPresentable B κ) (i : A ⟶ B) (p : B ⟶ X)
      (u : r.R.obj (F.obj A) ⟶ F.obj B),
      i ≫ p = f ∧ r.unit.app (F.obj A) ≫ u = F.map i :=
  exists_weakReflection_transition F r hX A f

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`SerrePositivity.HomotopicalAlgebra.Smith.LocalPresentableCover,
        `SerrePositivity.HomotopicalAlgebra.Smith.WeakReflectionApproximation].contains
          env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Local-cover module was not audited"
  logInfo m!"Local presentable-cover audit passed: {count} declarations, standard axioms only."
