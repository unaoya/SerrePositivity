module
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 右 tensor 比較の帰納段階の自然性
概要：一つの結合比較で可換な四角形を、右側の一因子を加えた比較へ移す。
方針：値域の圏を抽象化し、tensor 合成と結合同型の自然性だけを使う。
規約：交差や反転は使わない。使われ方：有限鎖立方体の連結比較の自然性の帰納。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory

/-- 右側に一因子を加えた結合比較も、元の可換四角形を保つ。 -/
lemma monoidalRightTensor_step {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {M N R S U I : C} (f : M ⟶ N) (h : R ⟶ S)
    (d : R ⟶ M ⊗ U) (e : S ⟶ N ⊗ U) (he : h ≫ e = d ≫ (f ⊗ₘ 𝟙 U)) :
    (h ⊗ₘ 𝟙 I) ≫ (e ⊗ₘ 𝟙 I) ≫ (α_ N U I).hom =
      (d ⊗ₘ 𝟙 I) ≫ (α_ M U I).hom ≫ (f ⊗ₘ 𝟙 (U ⊗ I)) := by
  have ht : (d ≫ (f ⊗ₘ 𝟙 U)) ⊗ₘ 𝟙 I =
      (d ⊗ₘ 𝟙 I) ≫ ((f ⊗ₘ 𝟙 U) ⊗ₘ 𝟙 I) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, he, ht,
    Category.assoc, associator_naturality]
  simp only [tensorHom_id, id_whiskerRight]

end SerrePositivity.KST.SConstruction
