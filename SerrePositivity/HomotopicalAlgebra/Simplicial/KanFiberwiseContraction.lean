module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTwoHornLift
public import SerrePositivity.HomotopicalAlgebra.Simplicial.CurriedHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-! # Correct a retraction homotopy to be constant over its Kan-fibration base

The correction fills the two-horn with the original homotopy and its
section-projected loop. No model structure or weak-equivalence axiom is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanFiberwiseContraction

private lemma face_zero_sigma :
    SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ := by
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  have h : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      𝟙 (SimplexCategory.mk 1) := by decide
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

private lemma face_one_sigma :
    SSet.stdSimplex.δ.{v} (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ := by
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  have h : SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      𝟙 (SimplexCategory.mk 1) := by decide
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

private lemma face_two_sigma :
    SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) =
      SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  have h : SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by decide
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp]
  rfl

private lemma vertex_zero :
    SSet.stdSimplex.δ.{v} (1 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

private lemma vertex_one :
    SSet.stdSimplex.δ.{v} (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

variable {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
  (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (H : SSet.Homotopy (𝟙 E) (p ≫ s))

def sectionLoop : SSet.Homotopy (p ≫ s) (p ≫ s) :=
  LargeParameterSquare.changeEndpoints (HomotopyClasses.postHomotopy (p ≫ s) H)
    (Category.id_comp _) (by
      rw [Category.assoc p s (p ≫ s), ← Category.assoc s p s, hs, Category.id_comp])

def baseLoop : SSet.Homotopy p p :=
  LargeParameterSquare.changeEndpoints (HomotopyClasses.postHomotopy p H)
    (Category.id_comp _) (by simp only [Category.assoc, hs, Category.comp_id])

lemma sectionLoop_h : (sectionLoop p s hs H).h = H.h ≫ (p ≫ s) := by
  rw [sectionLoop, LargeParameterSquare.changeEndpoints_h]
  rfl

lemma baseLoop_h : (baseLoop p s hs H).h = H.h ≫ p := by
  rw [baseLoop, LargeParameterSquare.changeEndpoints_h]
  rfl

include hp hs H in
lemma exists_homotopy : ∃ V : SSet.Homotopy (𝟙 E) (p ≫ s),
    V.h ≫ p = fst E (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)) ≫ p := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  have hq : SSet.modelCategoryQuillen.J.rlp ((ihom E).map p) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  let e₀ := curry (sectionLoop p s hs H).h
  let e₁ := curry H.h
  let b := SSet.stdSimplex.σ (0 : Fin 2) ≫ curry (baseLoop p s hs H).h
  have hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ e₀ =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ e₁ :=
    (LargeParameterSquare.edge_one (sectionLoop p s hs H)).trans
      (LargeParameterSquare.edge_one H).symm
  have h₀ : e₀ ≫ (ihom E).map p = SSet.stdSimplex.δ (0 : Fin 3) ≫ b := by
    dsimp only [e₀, b]
    rw [← Category.assoc, face_zero_sigma, Category.id_comp, ← curry_natural_right]
    rw [sectionLoop_h, baseLoop_h]
    simp only [Category.assoc, hs, Category.comp_id]
  have h₁ : e₁ ≫ (ihom E).map p = SSet.stdSimplex.δ (1 : Fin 3) ≫ b := by
    dsimp only [e₁, b]
    rw [← Category.assoc, face_one_sigma, Category.id_comp, ← curry_natural_right]
    rw [baseLoop_h]
  obtain ⟨t, ht₀, ht₁, htp⟩ := KanTwoHornLift.exists_triangle ((ihom E).map p) hq e₀ e₁ b hc h₀ h₁
  have hz : SSet.stdSimplex.δ (1 : Fin 2) ≫ (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) =
      LargeParameterSquare.point (𝟙 E) := by
    rw [← Category.assoc, vertex_zero, Category.assoc, ht₁]
    exact LargeParameterSquare.edge_zero H
  have ho : SSet.stdSimplex.δ (0 : Fin 2) ≫ (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) =
      LargeParameterSquare.point (p ≫ s) := by
    rw [← Category.assoc, vertex_one, Category.assoc, ht₀]
    exact LargeParameterSquare.edge_zero (sectionLoop p s hs H)
  refine ⟨CurriedHomotopy.ofEdge (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) hz ho, ?_⟩
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) ≫ p = _
  rw [← uncurry_natural_right, Category.assoc, htp]
  dsimp only [b]
  rw [← Category.assoc, face_two_sigma, Category.assoc,
    LargeParameterSquare.edge_zero (baseLoop p s hs H), uncurry_natural_left,
    LargeParameterSquare.point, uncurry_curry]
  rfl

end SerrePositivity.SimplicialModel.KanFiberwiseContraction
