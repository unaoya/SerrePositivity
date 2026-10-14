module

public import SerrePositivity.Spectra.ModelCategory.LevelClasses
public import SerrePositivity.Spectra.General.Limits
public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness

/-! # Smallness of the free-level generators

A common regular cardinal for the domains of the generating maps is transported
through F_n by its evaluation adjoint. This proves the image small-object
hypothesis rather than assuming it. The generator class must be small, and the
ambient hom-universe and colimit assumptions are recorded explicitly.
-/

@[expose] public section
universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumLevelModel

lemma isSmall_strictMap {C D : Type*} [Category* C] [Category* D]
    (P : MorphismProperty C) [P.IsSmall.{w}] (F : C ⥤ D) :
    (P.strictMap F).IsSmall.{w} :=
  SerrePositivity.ModelGeneration.EvaluationFamily.isSmall_strictMap P F

lemma isSmall_of_smallObjectArgument {C : Type*} [Category* C]
    (P : MorphismProperty C) [P.HasSmallObjectArgument.{w}] : P.IsSmall.{w} :=
  SerrePositivity.ModelGeneration.EvaluationFamily.isSmall_of_smallObjectArgument P

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{w, w} C] (K : C)
  [LocallySmall.{w} (GeneralSymmetricSpectrum C K)]

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{w, w} C]
  [LocallySmall.{w} (GeneralSymmetricSpectrum C K)] in
lemma levelGenerators_isSmall (P : MorphismProperty C) [P.IsSmall.{w}] :
    (levelGenerators K P).IsSmall.{w} := by
  have : ∀ n : ℕ, (P.strictMap (freeAt (K := K) n)).IsSmall.{w} :=
    fun n ↦ isSmall_strictMap P (freeAt n)
  exact MorphismProperty.isSmall_iSup _

/-- A common presentability cardinal of generator domains suffices for the
free-level small-object argument. -/
lemma levelGenerators_smallObjectArgument (P : MorphismProperty C) [P.IsSmall.{w}]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hP : ∀ {A B : C} (i : A ⟶ B), P i → IsCardinalPresentable A κ) :
    (levelGenerators K P).HasSmallObjectArgument.{w} := by
  let : ∀ n : ℕ, PreservesColimitsOfSize.{w, w} (evaluation (K := K) n) := fun _ ↦ {}
  exact SerrePositivity.ModelGeneration.EvaluationFamily.generators_smallObjectArgument.{w}
    (fun n : ℕ ↦ freeAt (K := K) n) (fun n ↦ evaluation n) (fun n ↦ freeAtAdjunction n) P κ hP

end SerrePositivity.SpectrumLevelModel
