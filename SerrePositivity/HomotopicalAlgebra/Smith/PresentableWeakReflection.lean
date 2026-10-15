module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLiftingClosure
public import SerrePositivity.HomotopicalAlgebra.Smith.PresentableFullInclusion
public import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-! # Presentable objects in a weakly reflective full subcategory

A weak reflection preserving κ-presentable objects provides cocones for all
κ-small diagrams of κ-presentable objects in the subcategory. The construction
retains the maps to a fixed object of the subcategory.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C]

structure PresentableWeakReflection (P : ObjectProperty C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] where
  R : C ⥤ C
  unit : 𝟭 C ⟶ R
  obj_mem (X : C) : P (R.obj X)
  preservesPresentable : R.PreservesCardinalPresentable κ
  factor {X Y : C} (hY : P Y) (f : X ⟶ Y) :
    ∃ g : R.obj X ⟶ Y, unit.app X ≫ g = f

namespace PresentableWeakReflection
variable {P : ObjectProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
  (r : PresentableWeakReflection P κ)

abbrev presentables (_ : PresentableWeakReflection P κ) : ObjectProperty C :=
  P ⊓ isCardinalPresentable C κ

lemma costructured_isCardinalFiltered [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
    (X : C) (hX : P X) :
    IsCardinalFiltered (CostructuredArrow r.presentables.ι X) κ where
  nonempty_cocone {J} _ F hJ := by
    let G := F ⋙ CostructuredArrow.proj r.presentables.ι X ⋙ r.presentables.ι
    have : ∀ j, IsCardinalPresentable (G.obj j) κ := fun j ↦ (F.obj j).left.property.2
    have : IsCardinalPresentable (colimit G) κ :=
      isCardinalPresentable_of_isColimit _ (colimit.isColimit G) κ hJ
    have := r.preservesPresentable
    have hR : IsCardinalPresentable (r.R.obj (colimit G)) κ := inferInstance
    let c : Cocone G :=
      { pt := X
        ι := { app j := (F.obj j).hom
               naturality j k f := by
                 change (F.map f).left.hom ≫ (F.obj k).hom = (F.obj j).hom ≫ 𝟙 X
                 rw [Category.comp_id]
                 exact (F.map f).w } }
    obtain ⟨g, hg⟩ := r.factor hX (colimit.desc G c)
    let Y : r.presentables.FullSubcategory := ⟨r.R.obj (colimit G), r.obj_mem _, hR⟩
    refine ⟨{ pt := CostructuredArrow.mk (Y := Y) g
              ι := { app j := CostructuredArrow.homMk
                       (ObjectProperty.homMk (colimit.ι G j ≫ r.unit.app (colimit G))) ?_
                     naturality j k f := ?_ } }⟩
    · change (colimit.ι G j ≫ r.unit.app (colimit G)) ≫ g = (F.obj j).hom
      rw [Category.assoc, hg]
      exact colimit.ι_desc c j
    · apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      dsimp
      simp only [Category.comp_id]
      change G.map f ≫ (colimit.ι G k ≫ r.unit.app (colimit G)) =
        colimit.ι G j ≫ r.unit.app (colimit G)
      rw [← Category.assoc, colimit.w G f]

abbrev toPresentables : r.presentables.FullSubcategory ⥤
    (isCardinalPresentable C κ).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.2)

lemma costructured_pre_final [IsCardinalLocallyPresentable C κ]
    (X : C) (hX : P X) :
    (CostructuredArrow.pre r.toPresentables (isCardinalPresentable C κ).ι X).Final := by
  have := r.preservesPresentable
  have := isFiltered_of_isCardinalFiltered
    (CostructuredArrow (isCardinalPresentable C κ).ι X) κ
  apply Functor.final_of_exists_of_isFiltered_of_fullyFaithful
  intro f
  let Y : r.presentables.FullSubcategory :=
    ⟨r.R.obj f.left.obj, r.obj_mem _, inferInstance⟩
  obtain ⟨g, hg⟩ := r.factor hX f.hom
  exact ⟨CostructuredArrow.mk (Y := Y) g,
    ⟨CostructuredArrow.homMk (ObjectProperty.homMk (r.unit.app f.left.obj)) hg⟩⟩

noncomputable def denseAt [IsCardinalLocallyPresentable C κ]
    (X : C) (hX : P X) : r.presentables.ι.DenseAt X := by
  have := r.costructured_pre_final X hX
  exact ((isCardinalPresentable C κ).ι.denseAt X).precompOfFinal r.toPresentables

abbrev toSubcategory : r.presentables.FullSubcategory ⥤ P.FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.1)

noncomputable def denseAtInSubcategory [IsCardinalLocallyPresentable C κ]
    (X : P.FullSubcategory) : r.toSubcategory.DenseAt X := by
  let e := (CostructuredArrow.post r.toSubcategory P.ι X).asEquivalence
  apply isColimitOfReflects P.ι
  exact (r.denseAt X.obj X.property).whiskerEquivalence e

lemma costructuredInSubcategory_isCardinalFiltered
    [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] (X : P.FullSubcategory) :
    IsCardinalFiltered (CostructuredArrow r.toSubcategory X) κ := by
  have : IsCardinalFiltered
      (CostructuredArrow (r.toSubcategory ⋙ P.ι) (P.ι.obj X)) κ :=
    r.costructured_isCardinalFiltered X.obj X.property
  exact IsCardinalFiltered.of_equivalence κ
    (CostructuredArrow.post r.toSubcategory P.ι X).asEquivalence.symm

include r in
/-- A bounded weak reflection and an accessible full inclusion give an
explicit small presentable generating family, not a full-image assumption. -/
lemma isCardinalAccessibleCategory [IsCardinalLocallyPresentable C κ]
    [HasCardinalFilteredColimits.{w} P.FullSubcategory κ]
    [P.ι.IsCardinalAccessible κ] : IsCardinalAccessibleCategory P.FullSubcategory κ := by
  have : ObjectProperty.EssentiallySmall.{w} r.presentables :=
    ObjectProperty.EssentiallySmall.of_le (Q := isCardinalPresentable C κ) inf_le_right
  have : r.toSubcategory.IsDense := ⟨fun X ↦ ⟨r.denseAtInSubcategory X⟩⟩
  have : ∀ X, IsCardinalFiltered (CostructuredArrow r.toSubcategory X) κ :=
    fun X ↦ r.costructuredInSubcategory_isCardinalFiltered X
  have : ∀ Y, IsCardinalPresentable (r.toSubcategory.obj Y) κ := fun Y ↦ by
    have : IsCardinalPresentable (P.ι.obj (r.toSubcategory.obj Y)) κ := Y.property.2
    exact presentable_of_accessible_fullyFaithful P.ι κ (r.toSubcategory.obj Y)
  have hgen := IsCardinalFilteredGenerator.of_isDense r.toSubcategory κ
  exact { toHasCardinalFilteredGenerator := hgen.hasCardinalFilteredGenerator }

end PresentableWeakReflection
end SerrePositivity.Smith
