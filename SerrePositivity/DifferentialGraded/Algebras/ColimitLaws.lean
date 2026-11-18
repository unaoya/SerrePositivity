module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# 共同全射族でのモノイド公理の検査

概要：単位と積を保つ共同全射族から元の頂点のモノイド三律を得る。
方針：単位則は一重入力、結合則は三重入力で元のモノイドへ戻す。
規約：各構造射の全射性やモノイド性を先に仮定しない。
使われ方：底の sifted 余極限のモノイド構造。
-/

@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {J : Type w}
  (X : C) (B : J → Mon C) (p : ∀ j, (B j).X ⟶ X)
  (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X)
  (ho : ∀ j, η[(B j).X] ≫ p j = one)
  (hm : ∀ j, μ[(B j).X] ≫ p j = (p j ⊗ₘ p j) ≫ mul)
  (hl : ∀ {T : C} (f g : 𝟙_ C ⊗ X ⟶ T),
    (∀ j, (𝟙_ C ◁ p j) ≫ f = (𝟙_ C ◁ p j) ≫ g) → f = g)
  (hr : ∀ {T : C} (f g : X ⊗ 𝟙_ C ⟶ T),
    (∀ j, (p j ▷ 𝟙_ C) ≫ f = (p j ▷ 𝟙_ C) ≫ g) → f = g)
  (ht : ∀ {T : C} (f g : (X ⊗ X) ⊗ X ⟶ T),
    (∀ j, ((p j ⊗ₘ p j) ⊗ₘ p j) ≫ f = ((p j ⊗ₘ p j) ⊗ₘ p j) ≫ g) → f = g)

include ho hm hl in
/-- 概要：降りた単位・積の左単位則。
方針：左単位をテンソルした構造射で検査する。
規約：元の left unitor を使う。
使われ方：余極限モノイドの第一の公理。 -/
lemma colimit_one_mul : (one ▷ X) ≫ mul = (λ_ X).hom := by
  apply hl
  intro j
  calc
    _ = (one ⊗ₘ p j) ≫ mul := by rw [tensorHom_def', Category.assoc]
    _ = ((η[(B j).X] ≫ p j) ⊗ₘ p j) ≫ mul := by rw [ho]
    _ = (η[(B j).X] ▷ (B j).X) ≫ (p j ⊗ₘ p j) ≫ mul := by
      simp only [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = (η[(B j).X] ▷ (B j).X) ≫ μ[(B j).X] ≫ p j := by rw [← hm]
    _ = _ := by rw [← Category.assoc, MonObj.one_mul, leftUnitor_naturality]

include ho hm hr in
/-- 概要：降りた単位・積の右単位則。
方針：右単位をテンソルした構造射で検査する。
規約：元の right unitor を使う。
使われ方：余極限モノイドの第二の公理。 -/
lemma colimit_mul_one : (X ◁ one) ≫ mul = (ρ_ X).hom := by
  apply hr
  intro j
  calc
    _ = (p j ⊗ₘ one) ≫ mul := by rw [tensorHom_def, Category.assoc]
    _ = (p j ⊗ₘ (η[(B j).X] ≫ p j)) ≫ mul := by rw [ho]
    _ = ((B j).X ◁ η[(B j).X]) ≫ (p j ⊗ₘ p j) ≫ mul := by
      simp only [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = ((B j).X ◁ η[(B j).X]) ≫ μ[(B j).X] ≫ p j := by rw [← hm]
    _ = _ := by rw [← Category.assoc, MonObj.mul_one, rightUnitor_naturality]

include hm ht in
/-- 概要：降りた積の結合則。
方針：三重テンソルの構造射で検査して元の結合則へ戻す。
規約：元の associator に沿った等式。
使われ方：余極限モノイドの第三の公理。 -/
lemma colimit_mul_assoc : (mul ▷ X) ≫ mul =
    (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by
  apply ht
  intro j
  calc
    _ = ((μ[(B j).X] ≫ p j) ⊗ₘ p j) ≫ mul := by
      simp only [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom,
        Category.comp_id]
      rw [← hm j]
    _ = (μ[(B j).X] ▷ (B j).X) ≫ μ[(B j).X] ≫ p j := by
      calc
        _ = (μ[(B j).X] ▷ (B j).X) ≫ (p j ⊗ₘ p j) ≫ mul := by
          simp only [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
        _ = _ := by rw [← hm j]
    _ = (α_ (B j).X (B j).X (B j).X).hom ≫
        ((B j).X ◁ μ[(B j).X]) ≫ (p j ⊗ₘ p j) ≫ mul := by
      rw [← Category.assoc, MonObj.mul_assoc]
      simp only [Category.assoc, ← hm]
    _ = (α_ (B j).X (B j).X (B j).X).hom ≫
        (p j ⊗ₘ (μ[(B j).X] ≫ p j)) ≫ mul := by
      simp only [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = _ := by
      rw [hm]
      simp only [← id_tensorHom, ← Category.assoc, associator_naturality]
      simp only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- 概要：共同全射族から頂点のモノイド構造を束ねる。
方針：三つの検査済みの律を使う。
規約：元の one と mul を定義上そのまま保持する。
使われ方：余極限の頂点のモノイド化。 -/
@[instance_reducible]
def monoidOfJointlyEpic : MonObj X where
  one := one
  mul := mul
  one_mul := _root_.SerrePositivity.DGAlgebra.colimit_one_mul X B p one mul ho hm hl
  mul_one := _root_.SerrePositivity.DGAlgebra.colimit_mul_one X B p one mul ho hm hr
  mul_assoc := _root_.SerrePositivity.DGAlgebra.colimit_mul_assoc X B p mul hm ht

end SerrePositivity.DGAlgebra
