module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedMiddleComposition
/-!
概要：全 Hom 自然な比較を、実合成作用の二つの全パラメータ写像へ移す。
方針：閉射の中間交換則と、豊穣合成の終点自然性を使う。
規約：次数零の通常射だけに制限しない。使われ方：実分解変更の合成保存。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  (C : Type w) [Category.{z} C] [EnrichedOrdinaryCategory V C]
/-- 全パラメータの豊穣合成は、同じ終点閉射の後合成を保つ。 -/
lemma enrichedComposition_target_parameter {K L : V} {P X Y Y' : C}
    (f : K ⟶ (P ⟶[V] X)) (g : L ⟶ (X ⟶[V] Y)) (b : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ eComp V P X Y ≫ eHomWhiskerLeft V P b =
      (f ⊗ₘ (g ≫ eHomWhiskerLeft V X b)) ≫ eComp V P X Y' := by
  rw [eComp_eHomWhiskerLeft, ← Category.assoc, tensorHom_comp_whiskerLeft]
/-- 同じ全 Hom 自然な四角形は、元の全パラメータ合成作用を保つ。 -/
lemma enrichedComposition_natural_parameter {K L : V} {P X Y X' Y' : C}
    (c : K ⟶ (P ⟶[V] X)) (f : L ⟶ (X ⟶[V] Y)) (g : L ⟶ (X' ⟶[V] Y'))
    (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ eHomWhiskerLeft V X b = g ≫ eHomWhiskerRight V a Y') :
    ((c ≫ eHomWhiskerLeft V P a) ⊗ₘ g) ≫ eComp V P X' Y' =
      (c ⊗ₘ f) ≫ eComp V P X Y ≫ eHomWhiskerLeft V P b := by
  rw [← tensorHom_comp_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_middle,
    ← Category.assoc, tensorHom_comp_whiskerLeft, ← h,
    enrichedComposition_target_parameter V C]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
