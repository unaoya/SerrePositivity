module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing

/-! # All six faces of the two degenerate triangle parameters -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.TriangleDegeneracyParameters
abbrev interval := SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)
abbrev sigma (i : Fin 2) : SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ interval :=
  SSet.stdSimplex.map (SimplexCategory.σ i)

lemma face0_sigma0 : SSet.stdSimplex.δ (0 : Fin 3) ≫ sigma 0 = 𝟙 _ := by
  have h : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      𝟙 (SimplexCategory.mk 1) := by decide
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

lemma face1_sigma0 : SSet.stdSimplex.δ (1 : Fin 3) ≫ sigma 0 = 𝟙 _ := by
  have h : SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      𝟙 (SimplexCategory.mk 1) := by decide
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

lemma face1_sigma1 : SSet.stdSimplex.δ (1 : Fin 3) ≫ sigma 1 = 𝟙 _ := by
  have h : SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
      𝟙 (SimplexCategory.mk 1) := by decide
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (1 : Fin 2)) = _
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

lemma face2_sigma1 : SSet.stdSimplex.δ (2 : Fin 3) ≫ sigma 1 = 𝟙 _ := by
  have h : SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
      𝟙 (SimplexCategory.mk 1) := by decide
  change SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (1 : Fin 2)) = _
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

lemma face0_sigma1 : SSet.stdSimplex.δ (0 : Fin 3) ≫ sigma 1 =
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1) := by
  have h : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (0 : Fin 2) := by decide
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (1 : Fin 2)) = _
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp]
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.δ (0 : Fin 2) = _
  rw [SSet.stdSimplex.δ_zero_eq_const, SSet.comp_const]

lemma face2_sigma0 : SSet.stdSimplex.δ (2 : Fin 3) ≫ sigma 0 =
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) := by
  have h : SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by decide
  change SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 2)) = _
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp]
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.δ (1 : Fin 2) = _
  rw [SSet.stdSimplex.δ_one_eq_const, SSet.comp_const]

lemma tensor_const_zero (P K : SSet.{v}) :
    P ◁ (SSet.const (X := K) (SSet.stdSimplex.obj₀Equiv.symm 0)) =
      fst P K ≫ SSet.ι₀ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [whiskerLeft_fst, Category.assoc, SSet.ι₀_fst, Category.comp_id]
  · rw [whiskerLeft_snd, Category.assoc, SSet.ι₀_snd, SSet.comp_const, SSet.comp_const]

lemma tensor_const_one (P K : SSet.{v}) :
    P ◁ (SSet.const (X := K) (SSet.stdSimplex.obj₀Equiv.symm 1)) =
      fst P K ≫ SSet.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [whiskerLeft_fst, Category.assoc, SSet.ι₁_fst, Category.comp_id]
  · rw [whiskerLeft_snd, Category.assoc, SSet.ι₁_snd, SSet.comp_const, SSet.comp_const]

end SerrePositivity.SimplicialModel.TriangleDegeneracyParameters
