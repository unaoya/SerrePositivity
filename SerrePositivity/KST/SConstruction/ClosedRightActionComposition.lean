module
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # 閉構造での右作用の合成と curry
概要：実右作用の合成等号を、関手空間の元の豊穣合成の保存へ移す。
方針：curry の随伴と元の評価の自然性で二回作用を回収する。
規約：積の対称性は使わない。使われ方：全 native Perf 関手族の合成保存。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed
variable {C : Type u} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- 二つの右作用の curry を豊穣合成すると、uncurry は元の同じ二回作用になる。 -/
lemma uncurry_curry_tensor_comp {X Y Z P Q : C} (f : X ⊗ P ⟶ Y) (g : Y ⊗ Q ⟶ Z) :
    uncurry ((curry f ⊗ₘ curry g) ≫ MonoidalClosed.comp X Y Z) =
      (α_ X P Q).inv ≫ (f ⊗ₘ 𝟙 Q) ≫ g := by
  rw [uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
    MonoidalClosed.compTranspose_eq]
  simp only [← id_tensorHom, ← tensorHom_id]
  rw [associator_inv_naturality_assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    id_tensorHom, ← uncurry_eq, uncurry_curry]
  have h : (f ⊗ₘ curry g) = (f ⊗ₘ 𝟙 Q) ≫ (𝟙 Y ⊗ₘ curry g) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc]
  rw [id_tensorHom, ← uncurry_eq, uncurry_curry]

/-- 元の右作用が入力合成を保てば、その curry は元の豊穣合成を保つ。 -/
lemma rightActionCurry_comp {X Y Z P Q R : C}
    (f : X ⊗ P ⟶ Y) (g : Y ⊗ Q ⟶ Z) (h : X ⊗ R ⟶ Z) (m : P ⊗ Q ⟶ R)
    (hc : (f ⊗ₘ 𝟙 Q) ≫ g = (α_ X P Q).hom ≫ (𝟙 X ⊗ₘ m) ≫ h) :
    (curry f ⊗ₘ curry g) ≫ MonoidalClosed.comp X Y Z = m ≫ curry h := by
  apply uncurry_injective
  rw [uncurry_curry_tensor_comp, uncurry_natural_left, uncurry_curry, hc]
  simp only [Iso.inv_hom_id_assoc, id_tensorHom]

end SerrePositivity.KST.SConstruction
