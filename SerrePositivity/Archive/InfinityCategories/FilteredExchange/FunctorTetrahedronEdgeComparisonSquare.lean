module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorPostVertexIso

/-!
概要：同じ六辺の指定比較と四面の指定比較の表示から、三単体の比較の正方形を得る。
方針：第零面の指定自然性を使い、共有する三辺の比較とその逆を相殺する。
規約：四面と六辺の指定値を保持。使われ方：元の単位三三単体の三関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 四面の指定比較が同じ六辺の比較で表されるなら、元の二つの合成は厳密に一致する。 -/
lemma functorTetrahedronIso_square_of_edge_comparisons
    {C₀ C₁ C₂ C₃ : Type u} [Category.{v} C₀] [Category.{v} C₁]
    [Category.{v} C₂] [Category.{v} C₃]
    (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₂₃ : C₂ ⥤ C₃)
    (F₀₂ : C₀ ⥤ C₂) (F₁₃ : C₁ ⥤ C₃) (F₀₃ : C₀ ⥤ C₃)
    (e₀₁₂ : F₀₂ ≅ F₀₁ ⋙ F₁₂) (e₁₂₃ : F₁₃ ≅ F₁₂ ⋙ F₂₃)
    (e₀₁₃ : F₀₃ ≅ F₀₁ ⋙ F₁₃) (e₀₂₃ : F₀₃ ≅ F₀₂ ⋙ F₂₃)
    (x₀ : C₀) (x₁ : C₁) (x₂ : C₂) (x₃ : C₃)
    (b₀₁ : F₀₁.obj x₀ ≅ x₁) (b₁₂ : F₁₂.obj x₁ ≅ x₂) (b₂₃ : F₂₃.obj x₂ ≅ x₃)
    (b₀₂ : F₀₂.obj x₀ ≅ x₂) (b₁₃ : F₁₃.obj x₁ ≅ x₃) (b₀₃ : F₀₃.obj x₀ ≅ x₃)
    (h₀₁₂ : e₀₁₂.app x₀ = b₀₂ ≪≫ b₁₂.symm ≪≫ F₁₂.mapIso b₀₁.symm)
    (h₁₂₃ : e₁₂₃.app x₁ = b₁₃ ≪≫ b₂₃.symm ≪≫ F₂₃.mapIso b₁₂.symm)
    (h₀₁₃ : e₀₁₃.app x₀ = b₀₃ ≪≫ b₁₃.symm ≪≫ F₁₃.mapIso b₀₁.symm)
    (h₀₂₃ : e₀₂₃.app x₀ = b₀₃ ≪≫ b₂₃.symm ≪≫ F₂₃.mapIso b₀₂.symm) :
    e₀₁₃.app x₀ ≪≫ e₁₂₃.app (F₀₁.obj x₀) =
      e₀₂₃.app x₀ ≪≫ F₂₃.mapIso (e₀₁₂.app x₀) := by
  apply Iso.ext
  have hn := e₁₂₃.hom.naturality b₀₁.inv
  change F₁₃.map b₀₁.inv ≫ (e₁₂₃.app (F₀₁.obj x₀)).hom =
    (e₁₂₃.app x₁).hom ≫ F₂₃.map (F₁₂.map b₀₁.inv) at hn
  calc
    _ = b₀₃.hom ≫ b₁₃.inv ≫
        F₁₃.map b₀₁.inv ≫ (e₁₂₃.app (F₀₁.obj x₀)).hom := by
      rw [h₀₁₃]
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    _ = b₀₃.hom ≫ b₁₃.inv ≫
        (e₁₂₃.app x₁).hom ≫ F₂₃.map (F₁₂.map b₀₁.inv) := by rw [hn]
    _ = b₀₃.hom ≫ b₂₃.inv ≫
        F₂₃.map b₁₂.inv ≫ F₂₃.map (F₁₂.map b₀₁.inv) := by
      rw [h₁₂₃]
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, ← Category.assoc,
        Iso.inv_hom_id, Category.id_comp]
    _ = _ := by
      rw [h₀₂₃, h₀₁₂]
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
        Category.assoc]
      rw [← F₂₃.map_comp_assoc, b₀₂.inv_hom_id, F₂₃.map_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
