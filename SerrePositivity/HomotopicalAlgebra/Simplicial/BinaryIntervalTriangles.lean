module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyBinarySquare

/-! # The two actual triangles in a binary homotopy square

The comparison edge runs one specified interval while the other is
fixed at its first endpoint. The cone edges are the simultaneous
interval and the other interval with one input fixed at its last
endpoint. All maps are explicit; no Kan filling is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.BinaryIntervalTriangles
open ComparisonTriangleDegeneracy KanComparisonTriangle
variable {T A B K : SSet.{v}} {f₀ f₁ : T ⟶ A} {g₀ g₁ : T ⟶ B}
  (F : SSet.Homotopy f₀ f₁) (G : SSet.Homotopy g₀ g₁) (k : A ⊗ B ⟶ K)

abbrev firstFixed := HomotopyBinarySquare.simultaneous (KanActualHomotopy.refl f₁) G k
abbrev secondFixed := HomotopyBinarySquare.simultaneous F (KanActualHomotopy.refl g₁) k

abbrev lowerFamily : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  lift (T ◁ SSet.stdSimplex.σ (1 : Fin 2) ≫ F.h)
    (T ◁ SSet.stdSimplex.σ (0 : Fin 2) ≫ G.h) ≫ k

abbrev upperFamily : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  lift (T ◁ SSet.stdSimplex.σ (0 : Fin 2) ≫ F.h)
    (T ◁ SSet.stdSimplex.σ (1 : Fin 2) ≫ G.h) ≫ k

lemma lower_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ lowerFamily F G k =
    (firstFixed G k (f₁ := f₁)).h := by
  rw [lowerFamily, ← Category.assoc, comp_lift, collapse_end_interval, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ from
    face_collapse_zero (0 : Fin 2), whiskerLeft_id, Category.id_comp]
  rfl

lemma lower_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ lowerFamily F G k =
    (HomotopyBinarySquare.simultaneous F G k).h := by
  rw [lowerFamily, ← Category.assoc, comp_lift]
  have h₀ := face_collapse_zero.{v} (1 : Fin 2)
  have h₁ := face_collapse_one.{v} (0 : Fin 2)
  change SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ at h₀
  change SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ at h₁
  simp only [← Category.assoc, ← whiskerLeft_comp, h₀, h₁, whiskerLeft_id, Category.id_comp]
  rfl

lemma lower_two : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ lowerFamily F G k =
    lift F.h (fst T HomotopyBinarySquare.interval ≫ g₀) ≫ k := by
  rw [lowerFamily, ← Category.assoc, comp_lift, collapse_start_interval, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ from
    face_collapse_one (1 : Fin 2), whiskerLeft_id, Category.id_comp]

lemma upper_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ upperFamily F G k =
    (secondFixed F k (g₁ := g₁)).h := by
  rw [upperFamily, ← Category.assoc, comp_lift, collapse_end_interval, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ from
    face_collapse_zero (0 : Fin 2), whiskerLeft_id, Category.id_comp]
  rfl

lemma upper_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ upperFamily F G k =
    (HomotopyBinarySquare.simultaneous F G k).h := by
  rw [upperFamily, ← Category.assoc, comp_lift]
  have h₀ := face_collapse_zero.{v} (1 : Fin 2)
  have h₁ := face_collapse_one.{v} (0 : Fin 2)
  change SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ at h₀
  change SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ at h₁
  simp only [← Category.assoc, ← whiskerLeft_comp, h₀, h₁, whiskerLeft_id, Category.id_comp]
  rfl

lemma upper_two : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ upperFamily F G k =
    lift (fst T HomotopyBinarySquare.interval ≫ f₀) G.h ≫ k := by
  rw [upperFamily, ← Category.assoc, comp_lift, collapse_start_interval, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ from
    face_collapse_one (1 : Fin 2), whiskerLeft_id, Category.id_comp]

def lower : Data (HomotopyBinarySquare.simultaneous F G k) (firstFixed G k (f₁ := f₁)) where
  triangle := curry (lowerFamily F G k)
  face_zero := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, lower_zero]
  face_one := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, lower_one]

def upper : Data (HomotopyBinarySquare.simultaneous F G k) (secondFixed F k (g₁ := g₁)) where
  triangle := curry (upperFamily F G k)
  face_zero := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, upper_zero]
  face_one := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, upper_one]

lemma lower_comparison : (comparison _ _ (lower F G k)).h =
    lift F.h (fst T HomotopyBinarySquare.interval ≫ g₀) ≫ k := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ curry (lowerFamily F G k)) = _
  rw [uncurry_natural_left, uncurry_curry, lower_two]

lemma upper_comparison : (comparison _ _ (upper F G k)).h =
    lift (fst T HomotopyBinarySquare.interval ≫ f₀) G.h ≫ k := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ curry (upperFamily F G k)) = _
  rw [uncurry_natural_left, uncurry_curry, upper_two]

end SerrePositivity.SimplicialModel.BinaryIntervalTriangles
