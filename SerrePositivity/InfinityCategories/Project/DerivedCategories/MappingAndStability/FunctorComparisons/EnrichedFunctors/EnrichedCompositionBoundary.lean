module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.EnrichedMiddleComposition
public import Mathlib.CategoryTheory.Monoidal.Preadditive
/-!
概要：二つの実比較差の合成は、中間項が厳密に消えて実合成の比較差になる。
方針：左右端の豊穣自然性、中央閉射の交換、tensor の加法性を使う。
規約：任意の全パラメータを保持。使われ方：分解 dg 合成の比較 cochain の微分式。
-/
@[expose] public section
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [Preadditive V]
  [MonoidalPreadditive V]
/-- tensor の左引数の差は、実 tensor 射の差になる。 -/
lemma enrichedTensor_sub_left {P P' Q Q' : V} (f g : P ⟶ P') (h : Q ⟶ Q') :
    (f - g) ⊗ₘ h = f ⊗ₘ h - g ⊗ₘ h := by
  simp only [tensorHom_def]
  change ((tensorRight Q).map (f - g)) ≫ (P' ◁ h) = _
  rw [Functor.map_sub, Preadditive.sub_comp]
  rfl
/-- tensor の右引数の差も、同じ実 tensor 射の差になる。 -/
lemma enrichedTensor_sub_right {P P' Q Q' : V} (f : P ⟶ P') (g h : Q ⟶ Q') :
    f ⊗ₘ (g - h) = f ⊗ₘ g - f ⊗ₘ h := by
  simp only [tensorHom_def]
  change (f ▷ Q) ≫ ((tensorLeft P').map (g - h)) = _
  rw [Functor.map_sub, Preadditive.comp_sub]
  rfl
variable (C : Type w) [Category.{z} C] [EnrichedOrdinaryCategory V C]
/-- 全パラメータの実二差の合成では、中間の同じ閉射の寄与が厳密に相殺される。 -/
lemma enrichedComposition_boundary {X₀ X₁ X₂ Y₀ Y₁ Y₂ : C}
    (s₀ : X₀ ⟶ Y₀) (s₁ : X₁ ⟶ Y₁) (s₂ : X₂ ⟶ Y₂)
    {K L : V} (a : K ⟶ Y₀ ⟶[V] Y₁) (b : L ⟶ Y₁ ⟶[V] Y₂)
    (c : K ⟶ X₀ ⟶[V] X₁) (d : L ⟶ X₁ ⟶[V] X₂) :
    ((a ≫ eHomWhiskerRight V s₀ Y₁ - c ≫ eHomWhiskerLeft V X₀ s₁) ⊗ₘ b) ≫
        eComp V X₀ Y₁ Y₂ +
      (c ⊗ₘ (b ≫ eHomWhiskerRight V s₁ Y₂ - d ≫ eHomWhiskerLeft V X₁ s₂)) ≫
        eComp V X₀ X₁ Y₂ =
      (a ⊗ₘ b) ≫ eComp V Y₀ Y₁ Y₂ ≫ eHomWhiskerRight V s₀ Y₂ -
        (c ⊗ₘ d) ≫ eComp V X₀ X₁ X₂ ≫ eHomWhiskerLeft V X₀ s₂ := by
  have h₀ : (a ⊗ₘ b) ≫ eComp V Y₀ Y₁ Y₂ ≫ eHomWhiskerRight V s₀ Y₂ =
      ((a ≫ eHomWhiskerRight V s₀ Y₁) ⊗ₘ b) ≫ eComp V X₀ Y₁ Y₂ := by
    rw [eComp_eHomWhiskerRight, ← Category.assoc, tensorHom_comp_whiskerRight]
  have h₁ : ((c ≫ eHomWhiskerLeft V X₀ s₁) ⊗ₘ b) ≫ eComp V X₀ Y₁ Y₂ =
      (c ⊗ₘ (b ≫ eHomWhiskerRight V s₁ Y₂)) ≫ eComp V X₀ X₁ Y₂ := by
    rw [← tensorHom_comp_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_middle,
      ← Category.assoc, tensorHom_comp_whiskerLeft]
  have h₂ : (c ⊗ₘ d) ≫ eComp V X₀ X₁ X₂ ≫ eHomWhiskerLeft V X₀ s₂ =
      (c ⊗ₘ (d ≫ eHomWhiskerLeft V X₁ s₂)) ≫ eComp V X₀ X₁ Y₂ := by
    rw [eComp_eHomWhiskerLeft, ← Category.assoc, tensorHom_comp_whiskerLeft]
  rw [enrichedTensor_sub_left, enrichedTensor_sub_right,
    Preadditive.sub_comp, Preadditive.sub_comp, ← h₀, h₁, ← h₂]
  abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories
