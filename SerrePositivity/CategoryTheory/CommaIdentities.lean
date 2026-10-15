module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-! # Reflection of identity arrows by over and under projections

An over or under triangle whose varying side is an identity is itself an
identity. The statement uses the actual identity-arrow property, allowing
its use in strict degree inequalities without replacing identities by isos.
-/

@[expose] public section
universe v u
open CategoryTheory

namespace SerrePositivity.CommaIdentities
variable {C : Type u} [Category.{v} C]

lemma under_homMk {j X Y : C} (f : j ⟶ X) (g : j ⟶ Y) (h : X ⟶ Y)
    (hh : MorphismProperty.identities C h) (w : f ≫ h = g) :
    MorphismProperty.identities (Under j)
      (Under.homMk (U := Under.mk f) (V := Under.mk g) h w) := by
  cases hh
  have hfg : f = g := by simpa only [Category.comp_id] using w
  cases hfg
  have he : Under.homMk (U := Under.mk f) (V := Under.mk f) (𝟙 X) =
      𝟙 (Under.mk f) := by ext; rfl
  exact he.symm ▸ MorphismProperty.ofHoms.mk (Under.mk f)

lemma under_reflect {j : C} {f g : Under j} (φ : f ⟶ g)
    (hφ : MorphismProperty.identities C φ.right) :
    MorphismProperty.identities (Under j) φ := by
  obtain ⟨X, f, rfl⟩ := Under.mk_surjective f
  obtain ⟨Y, g, rfl⟩ := Under.mk_surjective g
  exact under_homMk f g φ.right hφ (Under.w φ)

lemma over_homMk {j X Y : C} (f : X ⟶ j) (g : Y ⟶ j) (h : X ⟶ Y)
    (hh : MorphismProperty.identities C h) (w : h ≫ g = f) :
    MorphismProperty.identities (Over j)
      (Over.homMk (U := Over.mk f) (V := Over.mk g) h w) := by
  cases hh
  have hgf : g = f := by simpa only [Category.id_comp] using w
  cases hgf
  have he : Over.homMk (U := Over.mk f) (V := Over.mk f) (𝟙 X) =
      𝟙 (Over.mk f) := by ext; rfl
  exact he.symm ▸ MorphismProperty.ofHoms.mk (Over.mk f)

lemma over_reflect {j : C} {f g : Over j} (φ : f ⟶ g)
    (hφ : MorphismProperty.identities C φ.left) :
    MorphismProperty.identities (Over j) φ := by
  obtain ⟨X, f, rfl⟩ := Over.mk_surjective f
  obtain ⟨Y, g, rfl⟩ := Over.mk_surjective g
  exact over_homMk f g φ.left hφ (Over.w φ)

end SerrePositivity.CommaIdentities
