module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! # Full simplicial homotopies are inverted by anodyne-inverting functors

Only the canonical interval and ordinary categorical inverses are used.
No full simplicial model structure is needed in the source universe.
-/

@[expose] public section
universe v vH uH
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.AnodyneHomotopy
variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

lemma endpoint_projection_zero (X : SSet.{v}) :
    SSet.ι₀ ≫ fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) = 𝟙 X := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

lemma endpoint_projection_one (X : SSet.{v}) :
    SSet.ι₁ ≫ fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) = 𝟙 X := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

include hL in
lemma endpoint_images_eq (X : SSet.{v}) :
    L.map (SSet.ι₀ (X := X)) = L.map (SSet.ι₁ (X := X)) := by
  let p := fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1))
  have : IsIso (L.map (SSet.ι₀ (X := X))) := hL _ (endpoint_zero_anodyne X)
  have hp₀ : L.map (SSet.ι₀ (X := X)) ≫ L.map p = 𝟙 _ := by
    rw [← L.map_comp, endpoint_projection_zero, L.map_id]
  have : IsIso (L.map p) := (isIso_comp_left_iff (L.map (SSet.ι₀ (X := X))) _).mp
    (hp₀.symm ▸ inferInstanceAs (IsIso (𝟙 (L.obj X))))
  apply (cancel_mono (L.map p)).mp
  rw [← L.map_comp, ← L.map_comp, endpoint_projection_zero, endpoint_projection_one]

include hL in
lemma map_homotopy_eq {X Y : SSet.{v}} {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    L.map f = L.map g := by
  calc
    L.map f = L.map SSet.ι₀ ≫ L.map h.h :=
      (congrArg L.map h.h₀).symm.trans (L.map_comp _ _)
    _ = L.map SSet.ι₁ ≫ L.map h.h :=
      congrArg (fun k => k ≫ L.map h.h) (endpoint_images_eq L hL X)
    _ = L.map g := (L.map_comp _ _).symm.trans (congrArg L.map h.h₁)

/-- The actual section and the same all-degree homotopy give an ordinary inverse. -/
def mapRetractionIso {X Y : SSet.{v}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (h : SSet.Homotopy (𝟙 X) (f ≫ s)) : L.obj X ≅ L.obj Y where
  hom := L.map f
  inv := L.map s
  hom_inv_id := (L.map_comp _ _).symm.trans
    ((map_homotopy_eq L hL h).symm.trans (L.map_id _))
  inv_hom_id := (L.map_comp _ _).symm.trans ((congrArg L.map hs).trans (L.map_id _))

/-- Ordinary localization of the canonical anodyne class, in any value universe. -/
abbrev anodyneQ := SSet.anodyneExtensions.{v}.Q

include hL in
lemma map_isIso_of_anodyneQ_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (anodyneQ.map f)) : IsIso (L.map f) := by
  let G := Localization.lift L hL anodyneQ
  let e : anodyneQ ⋙ G ≅ L := Localization.fac L hL anodyneQ
  have : IsIso (G.map (anodyneQ.map f)) := inferInstance
  let ea : Arrow.mk (G.map (anodyneQ.map f)) ≅ Arrow.mk (L.map f) :=
    Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm
  exact ((MorphismProperty.isomorphisms H).arrow_mk_iso_iff ea).mp inferInstance

end SerrePositivity.SimplicialModel.AnodyneHomotopy
