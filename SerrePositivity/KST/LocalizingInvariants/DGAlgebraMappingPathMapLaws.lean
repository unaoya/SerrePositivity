module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathMap

/-!
概要：mapping-path に沿う実正方形の射は、恒等と合成を厳密に保つ。
方針：実 pullback の両射影と経路関手の厳密な関手則で検査する。
規約：可換性の証人の選択に依存しない。使われ方：実 mapping-path 因子分解の関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
variable (R : Type u) [CommRing R]

lemma map_id {A B : Mon (Complex R)} (f : A ⟶ B) :
    map R f f (𝟙 A) (𝟙 B) (by simp) = 𝟙 (algebra R f) := by
  apply MonoidPullback.hom_ext (Path.source R B) f
  · change map R f f (𝟙 A) (𝟙 B) _ ≫ inclusion R f = 𝟙 _ ≫ inclusion R f
    rw [map_inclusion, Path.map_id, Category.comp_id, Category.id_comp]
  · change map R f f (𝟙 A) (𝟙 B) _ ≫ projection R f = 𝟙 _ ≫ projection R f
    rw [map_projection, Category.comp_id, Category.id_comp]

lemma map_comp {A₀ B₀ A₁ B₁ A₂ B₂ : Mon (Complex R)}
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)
    (a₀₁ : A₀ ⟶ A₁) (b₀₁ : B₀ ⟶ B₁) (w₀₁ : f₀ ≫ b₀₁ = a₀₁ ≫ f₁)
    (a₁₂ : A₁ ⟶ A₂) (b₁₂ : B₁ ⟶ B₂) (w₁₂ : f₁ ≫ b₁₂ = a₁₂ ≫ f₂) :
    map R f₀ f₂ (a₀₁ ≫ a₁₂) (b₀₁ ≫ b₁₂)
      (by rw [← Category.assoc, w₀₁, Category.assoc, w₁₂, ← Category.assoc]) =
        map R f₀ f₁ a₀₁ b₀₁ w₀₁ ≫ map R f₁ f₂ a₁₂ b₁₂ w₁₂ := by
  apply MonoidPullback.hom_ext (Path.source R B₂) f₂
  · change map R f₀ f₂ _ _ _ ≫ inclusion R f₂ =
      (map R f₀ f₁ _ _ _ ≫ map R f₁ f₂ _ _ _) ≫ inclusion R f₂
    rw [map_inclusion, Category.assoc, map_inclusion, ← Category.assoc, map_inclusion,
      Category.assoc, ← Path.map_comp]
  · change map R f₀ f₂ _ _ _ ≫ projection R f₂ =
      (map R f₀ f₁ _ _ _ ≫ map R f₁ f₂ _ _ _) ≫ projection R f₂
    rw [map_projection, Category.assoc, map_projection, map_projection_assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
