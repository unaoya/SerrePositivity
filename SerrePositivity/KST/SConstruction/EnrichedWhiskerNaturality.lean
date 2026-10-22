module
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! # 同じ全 Hom 自然性の合成と余錐からの降下
概要：全 Hom に自然な成分を合成し、余錐の各脚で自然性を検出する。
方針：前後合成の交換と通常成分の合成則を使う。
規約：候補関手の高次入力を保持。使われ方：写像円柱の源比較・射影。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  {D : Type w} [Category.{z} D] [EnrichedOrdinaryCategory V D]

/-- 元の二つの全 Hom 自然性は、同じ通常成分の合成にも成り立つ。 -/
lemma enriched_whisker_naturality_comp
    {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : D} {P : V}
    (a : P ⟶ (X₀ ⟶[V] X₁)) (b : P ⟶ (Y₀ ⟶[V] Y₁)) (c : P ⟶ (Z₀ ⟶[V] Z₁))
    (s₀ : X₀ ⟶ Y₀) (s₁ : X₁ ⟶ Y₁) (t₀ : Y₀ ⟶ Z₀) (t₁ : Y₁ ⟶ Z₁)
    (hs : a ≫ eHomWhiskerLeft V X₀ s₁ = b ≫ eHomWhiskerRight V s₀ Y₁)
    (ht : b ≫ eHomWhiskerLeft V Y₀ t₁ = c ≫ eHomWhiskerRight V t₀ Z₁) :
    a ≫ eHomWhiskerLeft V X₀ (s₁ ≫ t₁) =
      c ≫ eHomWhiskerRight V (s₀ ≫ t₀) Z₁ := by
  rw [eHomWhiskerLeft_comp, ← Category.assoc, hs, Category.assoc,
    ← eHom_whisker_exchange, ← Category.assoc, ht, Category.assoc,
    ← eHomWhiskerRight_comp]

/-- 元の余錐の脚に自然な全族から、降下成分の同じ脚への制限の自然性を得る。 -/
lemma enriched_cocone_desc_family
    {X Y QX QY TX TY : D} {P : V}
    (a : P ⟶ (X ⟶[V] Y)) (m : P ⟶ (QX ⟶[V] QY)) (b : P ⟶ (TX ⟶[V] TY))
    (j : X ⟶ QX) (k : Y ⟶ QY) (p : QX ⟶ TX) (q : QY ⟶ TY)
    (hm : m ≫ eHomWhiskerRight V j QY = a ≫ eHomWhiskerLeft V X k)
    (ha : a ≫ eHomWhiskerLeft V X (k ≫ q) =
      b ≫ eHomWhiskerRight V (j ≫ p) TY) :
    (m ≫ eHomWhiskerLeft V QX q) ≫ eHomWhiskerRight V j TY =
      (b ≫ eHomWhiskerRight V p TY) ≫ eHomWhiskerRight V j TY := by
  rw [Category.assoc, eHom_whisker_exchange, ← Category.assoc, hm,
    Category.assoc, ← eHomWhiskerLeft_comp, ha, eHomWhiskerRight_comp, Category.assoc]

end SerrePositivity.KST.SConstruction
