module
public import Mathlib.CategoryTheory.Enriched.Basic

/-! # 全 Hom の三重 tensor 作用の結合計算
概要：三つのパラメータの逐次作用を、元の豊穣合成の二段の式へ整理する。
方針：monoidal 結合写像の自然性・豊穣結合則・元の関手の合成保存を使う。
規約：パラメータや Hom を離散化しない。使われ方：二回の tensor dg 作用の比較。
-/
@[expose] public section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable (V : Type u) [Category V] [MonoidalCategory V]
  {C : Type v} [EnrichedCategory V C]

/-- 元の三つの Hom への作用は、monoidal と豊穣の結合則で二つの括弧を比較できる。 -/
lemma enrichedTensorTripleComposition {K L M : V} {X₀ X₁ X₂ X₃ : C}
    (a : K ⟶ (X₀ ⟶[V] X₁)) (b : L ⟶ (X₁ ⟶[V] X₂)) (c : M ⟶ (X₂ ⟶[V] X₃)) :
    (α_ K L M).hom ≫ (a ⊗ₘ ((b ⊗ₘ c) ≫ eComp V X₁ X₂ X₃)) ≫ eComp V X₀ X₁ X₃ =
      (((a ⊗ₘ b) ≫ eComp V X₀ X₁ X₂) ⊗ₘ c) ≫ eComp V X₀ X₂ X₃ := by
  have ht : (a ⊗ₘ ((b ⊗ₘ c) ≫ eComp V X₁ X₂ X₃)) =
      (a ⊗ₘ (b ⊗ₘ c)) ≫ (𝟙 (X₀ ⟶[V] X₁) ⊗ₘ eComp V X₁ X₂ X₃) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hs : (((a ⊗ₘ b) ≫ eComp V X₀ X₁ X₂) ⊗ₘ c) =
      ((a ⊗ₘ b) ⊗ₘ c) ≫ (eComp V X₀ X₁ X₂ ⊗ₘ 𝟙 (X₂ ⟶[V] X₃)) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [ht, hs]
  simp only [Category.assoc]
  rw [← associator_naturality_assoc, id_tensorHom, e_assoc', tensorHom_id]

variable {D : Type w} [EnrichedCategory V D]

/-- 内側の元の dg 作用をさらに写すことは、写した Hom の同じ二段合成になる。 -/
lemma enrichedFunctorTensorAction_composition (F : EnrichedFunctor V C D)
    {K L M : V} {x y z : C} {t : D}
    (a : K ⟶ (t ⟶[V] F.obj x)) (b : L ⟶ (x ⟶[V] y)) (c : M ⟶ (y ⟶[V] z)) :
    (α_ K L M).hom ≫ (𝟙 K ⊗ₘ ((b ⊗ₘ c) ≫ eComp V x y z)) ≫
        (a ⊗ₘ F.map x z) ≫ eComp V t (F.obj x) (F.obj z) =
      (((a ⊗ₘ (b ≫ F.map x y)) ≫ eComp V t (F.obj x) (F.obj y)) ⊗ₘ
        (c ≫ F.map y z)) ≫ eComp V t (F.obj y) (F.obj z) := by
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp, F.map_comp]
  exact enrichedTensorTripleComposition V a (b ≫ F.map x y) (c ≫ F.map y z)

end SerrePositivity.KST.SConstruction
