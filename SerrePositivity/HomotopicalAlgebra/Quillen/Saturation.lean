module

public import SerrePositivity.HomotopicalAlgebra.Quillen.WhiteheadConverse

/-! # Model weak equivalences are detected by ordinary localization

The converse direction is proved from cylinder lifting and the fundamental
lemma, then transported along actual cofibrant and fibrant resolutions.
No functorial factorization or combinatoriality hypothesis is needed.
-/

@[expose] public section
universe v u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

lemma leftHomotopyInverse_of_isIso_map {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [IsIso (L.map f)] :
    ∃ g : Y ⟶ X, LeftHomotopyRel (f ≫ g) (𝟙 X) ∧
      LeftHomotopyRel (g ≫ f) (𝟙 Y) := by
  obtain ⟨g, hg⟩ := (bijective_leftHomotopyClassToHom L Y X).surjective (inv (L.map f))
  obtain ⟨g, rfl⟩ := LeftHomotopyClass.mk_surjective g
  change L.map g = inv (L.map f) at hg
  refine ⟨g, ?_, ?_⟩
  · apply (LeftHomotopyClass.mk_eq_mk_iff _ _).mp
    apply (bijective_leftHomotopyClassToHom L X X).injective
    simp [hg]
  · apply (LeftHomotopyClass.mk_eq_mk_iff _ _).mp
    apply (bijective_leftHomotopyClassToHom L Y Y).injective
    simp [hg]

lemma weakEquivalence_of_isIso_map_of_bifibrant {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [IsIso (L.map f)] : weakEquivalences C f := by
  let d := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  have : Cofibration d.i := ⟨d.hi.1⟩
  have : WeakEquivalence d.i := ⟨d.hi.2⟩
  have : Fibration d.p := ⟨d.hp⟩
  have := isCofibrant_of_cofibration d.i
  have := isFibrant_of_fibration d.p
  have : IsIso (L.map d.i) := Localization.inverts L (weakEquivalences C) d.i d.hi.2
  have hfac : L.map d.i ≫ L.map d.p = L.map f := (L.map_comp _ _).symm.trans (congrArg L.map d.fac)
  have : IsIso (L.map d.p) := (isIso_comp_left_iff (L.map d.i) (L.map d.p)).mp
    (hfac.symm ▸ inferInstanceAs (IsIso (L.map f)))
  obtain ⟨g, hg₀, hg₁⟩ := leftHomotopyInverse_of_isIso_map L d.p
  have hp := weakEquivalence_of_fibration_leftHomotopyInverse d.p g hg₀ hg₁
  exact d.fac ▸ (weakEquivalences C).comp_mem d.i d.p d.hi.2 hp

lemma isIso_map_iff_of_weak_square {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : Arrow.mk f ⟶ Arrow.mk g) (hl : weakEquivalences C a.left)
    (hr : weakEquivalences C a.right) : IsIso (L.map f) ↔ IsIso (L.map g) := by
  have : IsIso (L.map a.left) := Localization.inverts L (weakEquivalences C) _ hl
  have : IsIso (L.map a.right) := Localization.inverts L (weakEquivalences C) _ hr
  have h : L.map a.left ≫ L.map g = L.map f ≫ L.map a.right :=
    (L.map_comp _ _).symm.trans ((congrArg L.map a.w).trans (L.map_comp _ _))
  rw [← isIso_comp_right_iff (L.map f) (L.map a.right), ← h,
    isIso_comp_left_iff]

/-- Ordinary localization detects exactly the original model weak equivalences. -/
lemma weakEquivalences_iff_isIso_map {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ IsIso (L.map f) := by
  constructor
  · exact Localization.inverts L (weakEquivalences C) f
  · intro hf
    let qf := CofibrantObject.HoCat.resolutionMap f
    let rqf := FibrantObject.HoCat.resolutionMap qf
    have hq : IsIso (L.map qf) :=
      (isIso_map_iff_of_weak_square L
        (Arrow.homMk (CofibrantObject.HoCat.pResolutionObj X)
          (CofibrantObject.HoCat.pResolutionObj Y)
          (CofibrantObject.HoCat.resolutionMap_fac f).symm)
        (mem_weakEquivalences (CofibrantObject.HoCat.pResolutionObj X))
        (mem_weakEquivalences (CofibrantObject.HoCat.pResolutionObj Y))).mpr hf
    have hrq : IsIso (L.map rqf) :=
      (isIso_map_iff_of_weak_square L
        (Arrow.homMk (FibrantObject.HoCat.iResolutionObj _)
          (FibrantObject.HoCat.iResolutionObj _)
          (FibrantObject.HoCat.resolutionMap_fac qf))
        (mem_weakEquivalences (FibrantObject.HoCat.iResolutionObj
          (CofibrantObject.HoCat.resolutionObj X)))
        (mem_weakEquivalences (FibrantObject.HoCat.iResolutionObj
          (CofibrantObject.HoCat.resolutionObj Y)))).mp hq
    have : WeakEquivalence rqf := ⟨weakEquivalence_of_isIso_map_of_bifibrant L rqf⟩
    have : WeakEquivalence qf := (FibrantObject.HoCat.weakEquivalence_resolutionMap_iff qf).mp
      inferInstance
    exact (weakEquivalence_iff f).mp
      ((CofibrantObject.HoCat.weakEquivalence_resolutionMap_iff f).mp inferInstance)

lemma weakEquivalences_eq_inverseImage_isomorphisms :
    weakEquivalences C = (MorphismProperty.isomorphisms H).inverseImage L := by
  ext X Y f
  exact weakEquivalences_iff_isIso_map L f

end SerrePositivity.Quillen
