module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedParameterizedUnit
/-!
概要：実閉射との豊穣合成を、同じ前後合成へ厳密に回収する。
方針：単位子の自然性と指定した閉射の豊穣 Hom を使う。
規約：全パラメータと全 cochain 次数を保持。使われ方：分解変更の厳密自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
lemma parameterEnriched_postcompose (V : Type u) [Category.{v} V] [MonoidalCategory V]
    (C : Type w) [Category C] [EnrichedOrdinaryCategory V C] (X Y Z : C) {K P : V}
    (i : 𝟙_ V ⟶ K) (a : K ⟶ (Y ⟶[V] Z)) (b : P ⟶ (X ⟶[V] Y))
    (g : Y ⟶ Z) (hi : i ≫ a = eHomEquiv V g) :
    (ρ_ P).inv ≫ P ◁ i ≫ (b ⊗ₘ a) ≫ eComp V X Y Z =
      b ≫ eHomWhiskerLeft V X g := by
  rw [whiskerLeft_comp_tensorHom_assoc, hi, tensorHom_def_assoc,
    ← rightUnitor_inv_naturality_assoc]
  rfl
lemma parameterEnriched_precompose (V : Type u) [Category.{v} V] [MonoidalCategory V]
    (C : Type w) [Category C] [EnrichedOrdinaryCategory V C] (X Y Z : C) {K P : V}
    (i : 𝟙_ V ⟶ K) (a : K ⟶ (X ⟶[V] Y)) (b : P ⟶ (Y ⟶[V] Z))
    (f : X ⟶ Y) (hi : i ≫ a = eHomEquiv V f) :
    (λ_ P).inv ≫ i ▷ P ≫ (a ⊗ₘ b) ≫ eComp V X Y Z =
      b ≫ eHomWhiskerRight V f Z := by
  rw [whiskerRight_comp_tensorHom_assoc, hi, tensorHom_def'_assoc,
    ← leftUnitor_inv_naturality_assoc]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
