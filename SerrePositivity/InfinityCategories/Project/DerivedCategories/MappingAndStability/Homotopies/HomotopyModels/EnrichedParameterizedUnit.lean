module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedIdentityWhiskering
/-!
概要：任意のパラメータからの射を、指定単位との豊穣合成から回収する。
方針：tensor の自然性と実豊穣単位律を使う。使われ方：出力分解の実単位律の射影。
-/
@[expose] public section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
/-- 指定した実単位を左に置いた豊穣合成は、同じ実パラメータ射を回収する。 -/
lemma parameterEnriched_leftUnit (V : Type u) [Category.{v} V] [MonoidalCategory V]
    (C : Type w) [EnrichedCategory V C] (X Y : C) {K P : V}
    (i : 𝟙_ V ⟶ K) (a : K ⟶ (X ⟶[V] X)) (b : P ⟶ (X ⟶[V] Y))
    (hi : i ≫ a = eId V X) :
    (λ_ P).inv ≫ i ▷ P ≫ (a ⊗ₘ b) ≫ eComp V X X Y = b := by
  rw [whiskerRight_comp_tensorHom_assoc, hi, tensorHom_def'_assoc,
    ← leftUnitor_inv_naturality_assoc, e_id_comp, Category.comp_id]
/-- 指定した実単位を右に置いても、同じ実パラメータ射を回収する。 -/
lemma parameterEnriched_rightUnit (V : Type u) [Category.{v} V] [MonoidalCategory V]
    (C : Type w) [EnrichedCategory V C] (X Y : C) {K P : V}
    (i : 𝟙_ V ⟶ K) (a : K ⟶ (Y ⟶[V] Y)) (b : P ⟶ (X ⟶[V] Y))
    (hi : i ≫ a = eId V Y) :
    (ρ_ P).inv ≫ P ◁ i ≫ (b ⊗ₘ a) ≫ eComp V X Y Y = b := by
  rw [whiskerLeft_comp_tensorHom_assoc, hi, tensorHom_def_assoc,
    ← rightUnitor_inv_naturality_assoc, e_comp_id, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
