module

public import SerrePositivity.HomotopicalAlgebra.Smith.PresentableWeakReflection

/-! # Local presentable covers generate an accessible full subcategory

A cover is allowed to depend on the map into the target object. No global
weak reflection or functorial choices of witnesses are required.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C]

structure LocalPresentableCover (P : ObjectProperty C) (κ : Cardinal.{w})
    [Fact κ.IsRegular] : Prop where
  cover {X : C} (hX : P X) (A : C) [IsCardinalPresentable A κ] (f : A ⟶ X) :
    ∃ (B : C) (_ : IsCardinalPresentable B κ) (_ : P B)
      (i : A ⟶ B) (p : B ⟶ X), i ≫ p = f

namespace LocalPresentableCover
variable {P : ObjectProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
  (h : LocalPresentableCover P κ)

abbrev presentables (_ : LocalPresentableCover P κ) : ObjectProperty C :=
  P ⊓ isCardinalPresentable C κ

abbrev toPresentables : h.presentables.FullSubcategory ⥤
    (isCardinalPresentable C κ).FullSubcategory := ObjectProperty.ιOfLE (fun _ hp ↦ hp.2)

abbrev toSubcategory : h.presentables.FullSubcategory ⥤ P.FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ hp ↦ hp.1)

lemma costructured_isCardinalFiltered [IsCardinalAccessibleCategory C κ]
    (X : C) (hX : P X) :
    IsCardinalFiltered (CostructuredArrow h.presentables.ι X) κ where
  nonempty_cocone {J} _ F hJ := by
    let H := F ⋙ CostructuredArrow.pre h.toPresentables (isCardinalPresentable C κ).ι X
    let c := IsCardinalFiltered.cocone (κ := κ) H hJ
    obtain ⟨B, hB, hPB, i, p, hip⟩ := h.cover hX c.pt.left.obj c.pt.hom
    let Y : h.presentables.FullSubcategory := ⟨B, hPB, hB⟩
    refine ⟨{ pt := CostructuredArrow.mk (Y := Y) p
              ι := { app j := CostructuredArrow.homMk
                       (ObjectProperty.homMk ((c.ι.app j).left.hom ≫ i)) ?_
                     naturality j k f := ?_ } }⟩
    · change ((c.ι.app j).left.hom ≫ i) ≫ p = (F.obj j).hom
      rw [Category.assoc, hip]
      exact (c.ι.app j).w
    · apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      dsimp
      simp only [Category.comp_id]
      change (F.map f).left.hom ≫ ((c.ι.app k).left.hom ≫ i) = (c.ι.app j).left.hom ≫ i
      rw [← Category.assoc]
      exact congrArg (fun a ↦ a ≫ i)
        (congrArg (fun a ↦ a.left.hom) (c.w f))

lemma costructured_pre_final [IsCardinalAccessibleCategory C κ]
    (X : C) (hX : P X) :
    (CostructuredArrow.pre h.toPresentables (isCardinalPresentable C κ).ι X).Final := by
  have := isFiltered_of_isCardinalFiltered
    (CostructuredArrow (isCardinalPresentable C κ).ι X) κ
  apply Functor.final_of_exists_of_isFiltered_of_fullyFaithful
  intro f
  obtain ⟨B, hB, hPB, i, p, hip⟩ := h.cover hX f.left.obj f.hom
  let Y : h.presentables.FullSubcategory := ⟨B, hPB, hB⟩
  exact ⟨CostructuredArrow.mk (Y := Y) p,
    ⟨CostructuredArrow.homMk (ObjectProperty.homMk i) hip⟩⟩

noncomputable def denseAt [IsCardinalAccessibleCategory C κ]
    (X : C) (hX : P X) : h.presentables.ι.DenseAt X := by
  have := h.costructured_pre_final X hX
  exact ((isCardinalPresentable C κ).ι.denseAt X).precompOfFinal h.toPresentables

noncomputable def denseAtInSubcategory [IsCardinalAccessibleCategory C κ]
    (X : P.FullSubcategory) : h.toSubcategory.DenseAt X := by
  let e := (CostructuredArrow.post h.toSubcategory P.ι X).asEquivalence
  apply isColimitOfReflects P.ι
  exact (h.denseAt X.obj X.property).whiskerEquivalence e

lemma costructuredInSubcategory_isCardinalFiltered [IsCardinalAccessibleCategory C κ]
    (X : P.FullSubcategory) :
    IsCardinalFiltered (CostructuredArrow h.toSubcategory X) κ := by
  have : IsCardinalFiltered
      (CostructuredArrow (h.toSubcategory ⋙ P.ι) (P.ι.obj X)) κ :=
    h.costructured_isCardinalFiltered X.obj X.property
  exact IsCardinalFiltered.of_equivalence κ
    (CostructuredArrow.post h.toSubcategory P.ι X).asEquivalence.symm

include h in
lemma isCardinalAccessibleCategory [IsCardinalAccessibleCategory C κ]
    [HasCardinalFilteredColimits.{w} P.FullSubcategory κ]
    [P.ι.IsCardinalAccessible κ] : IsCardinalAccessibleCategory P.FullSubcategory κ := by
  have : ObjectProperty.EssentiallySmall.{w} h.presentables :=
    ObjectProperty.EssentiallySmall.of_le (Q := isCardinalPresentable C κ) inf_le_right
  have : h.toSubcategory.IsDense := ⟨fun X ↦ ⟨h.denseAtInSubcategory X⟩⟩
  have : ∀ X, IsCardinalFiltered (CostructuredArrow h.toSubcategory X) κ :=
    fun X ↦ h.costructuredInSubcategory_isCardinalFiltered X
  have : ∀ Y, IsCardinalPresentable (h.toSubcategory.obj Y) κ := fun Y ↦ by
    have : IsCardinalPresentable (P.ι.obj (h.toSubcategory.obj Y)) κ := Y.property.2
    exact presentable_of_accessible_fullyFaithful P.ι κ (h.toSubcategory.obj Y)
  have hgen := IsCardinalFilteredGenerator.of_isDense h.toSubcategory κ
  exact { toHasCardinalFilteredGenerator := hgen.hasCardinalFilteredGenerator }

end LocalPresentableCover

lemma PresentableWeakReflection.localCover {P : ObjectProperty C}
    {κ : Cardinal.{w}} [Fact κ.IsRegular] (r : PresentableWeakReflection P κ) :
    LocalPresentableCover P κ where
  cover hX A _ f := by
    have := r.preservesPresentable
    obtain ⟨p, hp⟩ := r.factor hX f
    exact ⟨r.R.obj A, inferInstance, r.obj_mem A, r.unit.app A, p, hp⟩

end SerrePositivity.Smith
