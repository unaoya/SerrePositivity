module

public import SerrePositivity.Spectra.ModelCategory.LevelClasses
public import SerrePositivity.Spectra.General.Limits
public import Mathlib.CategoryTheory.Presentable.Adjunction

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
    (P.strictMap F).IsSmall.{w} := by
  let φ : P.toSet → (P.strictMap F).toSet := fun a ↦
    ⟨F.mapArrow.obj a.1, P.map_mem_strictMap F a.1.hom a.2⟩
  have hs : Function.Surjective φ := by
    rintro ⟨⟨A, B, f⟩, hf⟩
    cases hf with
    | map hf => exact ⟨⟨Arrow.mk _, hf⟩, rfl⟩
  exact ⟨small_of_surjective hs⟩

lemma isSmall_of_smallObjectArgument {C : Type*} [Category* C]
    (P : MorphismProperty C) [P.HasSmallObjectArgument.{w}] : P.IsSmall.{w} := by
  obtain ⟨κ, hreg, hbot, hcard⟩ :=
    MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := P)
  let : Fact κ.IsRegular := hreg
  let : OrderBot κ.ord.ToType := hbot
  let : P.IsCardinalForSmallObjectArgument κ := hcard
  exact SmallObject.isSmall P κ

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
  have : (levelGenerators K P).IsSmall.{w} := levelGenerators_isSmall K P
  have : (levelGenerators K P).IsCardinalForSmallObjectArgument κ := by
    refine { preservesColimit := ?_ }
    intro A B X Y i hi f hf
    change (⨆ n : ℕ, P.strictMap (freeAt (K := K) n)) i at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, hi⟩ := hi
    cases hi with
    | @map A B i hi =>
      have : IsCardinalPresentable A κ := hP i hi
      let : PreservesColimitsOfSize.{w, w} (evaluation (K := K) n) := {}
      have : IsCardinalPresentable ((freeAt (K := K) n).obj A) κ :=
        (freeAtAdjunction n).isCardinalPresentable_leftAdjoint_obj κ A
      have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
        (coyoneda.obj (op ((freeAt (K := K) n).obj A))) κ κ.ord.ToType
      infer_instance
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩
end SerrePositivity.SpectrumLevelModel
