module
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 生成射に沿う余モノイド則の移送
概要：対角・増大を保つ射で、源の余結合・余単位則を標的の同じ射への制限へ移す。
方針：tensor 合成と元の結合・単位の自然性を使う。
規約：結合替えの向きを保持する。使われ方：cubical 鎖複体の余モノイド則の余極限降下。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M X : C} [ComonObj M] (g : M ⟶ X) (δ : X ⟶ X ⊗ X) (ε : X ⟶ 𝟙_ C)
  (hδ : g ≫ δ = ComonObj.comul ≫ (g ⊗ₘ g))
  (hε : g ≫ ε = ComonObj.counit)

include hδ hε in
/-- 源の左余単位律を、同じ生成射に沿って移す。 -/
lemma comonoidGenerator_left_counit :
    g ≫ (δ ≫ (ε ⊗ₘ 𝟙 X)) = g ≫ (λ_ X).inv := by
  rw [← Category.assoc, hδ, Category.assoc, tensorHom_comp_tensorHom,
    hε, Category.comp_id]
  exact ComonObj.counit_comul_hom g

include hδ hε in
/-- 源の右余単位律を、同じ生成射に沿って移す。 -/
lemma comonoidGenerator_right_counit :
    g ≫ (δ ≫ (𝟙 X ⊗ₘ ε)) = g ≫ (ρ_ X).inv := by
  rw [← Category.assoc, hδ, Category.assoc, tensorHom_comp_tensorHom,
    hε, Category.comp_id]
  exact ComonObj.comul_counit_hom g

include hδ in
/-- 源の余結合則を、同じ生成射に沿って移す。 -/
lemma comonoidGenerator_coassoc :
    g ≫ (δ ≫ (δ ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom) =
      g ≫ (δ ≫ (𝟙 X ⊗ₘ δ)) := by
  have hleft : (g ⊗ₘ g) ≫ (δ ⊗ₘ 𝟙 X) =
      (ComonObj.comul ⊗ₘ 𝟙 M) ≫ ((g ⊗ₘ g) ⊗ₘ g) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hδ]
  have hright : (𝟙 M ⊗ₘ ComonObj.comul) ≫ (g ⊗ₘ (g ⊗ₘ g)) =
      (g ⊗ₘ g) ≫ (𝟙 X ⊗ₘ δ) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hδ]
  calc
    _ = ComonObj.comul ≫ ((g ⊗ₘ g) ≫ (δ ⊗ₘ 𝟙 X)) ≫
        (α_ X X X).hom := by rw [← Category.assoc g δ, hδ]; simp only [Category.assoc]
    _ = ComonObj.comul ≫ (ComonObj.comul ⊗ₘ 𝟙 M) ≫
        ((g ⊗ₘ g) ⊗ₘ g) ≫ (α_ X X X).hom := by rw [hleft, Category.assoc]
    _ = ComonObj.comul ≫ (ComonObj.comul ⊗ₘ 𝟙 M) ≫
        (α_ M M M).hom ≫ (g ⊗ₘ (g ⊗ₘ g)) := by rw [associator_naturality]
    _ = ComonObj.comul ≫ (𝟙 M ⊗ₘ ComonObj.comul) ≫
        (g ⊗ₘ (g ⊗ₘ g)) := by
      simpa only [Category.assoc, tensorHom_id, id_tensorHom] using
        congrArg (fun f => f ≫ (g ⊗ₘ (g ⊗ₘ g))) (ComonObj.comul_assoc M).symm
    _ = ComonObj.comul ≫ (g ⊗ₘ g) ≫ (𝟙 X ⊗ₘ δ) := by rw [hright]
    _ = _ := by rw [← Category.assoc, ← hδ, Category.assoc]

end SerrePositivity.KST.SConstruction
