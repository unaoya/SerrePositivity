module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.EvaluationMorphismProperties
public import Mathlib.CategoryTheory.Presentable.Adjunction

/-! # Small-object arguments for free images of an evaluation family

A common regular presentability cardinal for source generator domains is
transported along all free/evaluation adjunctions. The index must be small in
the small-object universe, independently of the ambient object universes.
-/

@[expose] public section
universe w t u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace SerrePositivity.ModelGeneration.EvaluationFamily

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

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {ι : Type t} [Small.{w} ι] (L : ι → C ⥤ D) (R : ι → D ⥤ C) (adj : ∀ i, L i ⊣ R i)

lemma generators_isSmall (P : MorphismProperty C) [P.IsSmall.{w}] :
    (generators L P).IsSmall.{w} := by
  have : ∀ i, (P.strictMap (L i)).IsSmall.{w} := fun i ↦ isSmall_strictMap P (L i)
  exact MorphismProperty.isSmall_iSup _

variable [LocallySmall.{w} D] [HasColimitsOfSize.{w, w} D]

include adj in
/-- Prove image generator smallness from presentability, not an image-SOA assumption. -/
lemma generators_smallObjectArgument_of_accessible (P : MorphismProperty C) [P.IsSmall.{w}]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [∀ i, (R i).IsCardinalAccessible κ]
    (hP : ∀ {A B : C} (f : A ⟶ B), P f → IsCardinalPresentable A κ) :
    (generators L P).HasSmallObjectArgument.{w} := by
  have : (generators L P).IsSmall.{w} := generators_isSmall L P
  have : (generators L P).IsCardinalForSmallObjectArgument κ := by
    refine { preservesColimit := ?_ }
    intro A B X Y f hf g hg
    change (⨆ i, P.strictMap (L i)) f at hf
    rw [MorphismProperty.iSup_iff] at hf
    obtain ⟨i, hf⟩ := hf
    cases hf with
    | @map A B f hf =>
      have : IsCardinalPresentable A κ := hP f hf
      have : IsCardinalPresentable ((L i).obj A) κ :=
        (adj i).isCardinalPresentable_leftAdjoint_obj κ A
      have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
        (coyoneda.obj (op ((L i).obj A))) κ κ.ord.ToType
      infer_instance
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

variable [∀ i, PreservesColimitsOfSize.{w, w} (R i)]

include adj in
/-- Colimit-preserving evaluations are a sufficient special case of accessibility. -/
lemma generators_smallObjectArgument (P : MorphismProperty C) [P.IsSmall.{w}]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hP : ∀ {A B : C} (f : A ⟶ B), P f → IsCardinalPresentable A κ) :
    (generators L P).HasSmallObjectArgument.{w} := by
  let : ∀ i, (R i).IsCardinalAccessible κ := fun _ ↦ inferInstance
  exact generators_smallObjectArgument_of_accessible L R adj P κ hP

end SerrePositivity.ModelGeneration.EvaluationFamily
