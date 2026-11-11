module
public import Mathlib.CategoryTheory.Iso
/-!
概要：元の出力模型比較を、その指定射と可換四角形で照合する。
方針：同じ全関手射の前合成と tensor 評価、元の合成比較の自然性を使う。
規約：指定比較・計算上限を変更しない。使われ方：一般 cell 模型の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
lemma iso_three_step_square {T : Type*} [Category T]
    {X0 X1 Y0 Y1 Z0 Z1 W0 W1 : T}
    (A0 : X0 ≅ Y0) (A1 : X1 ≅ Y1) (B0 : Y0 ≅ Z0) (B1 : Y1 ≅ Z1)
    (C0 : Z0 ≅ W0) (C1 : Z1 ≅ W1)
    (x : X0 ⟶ X1) (y : Y0 ⟶ Y1) (z : Z0 ⟶ Z1) (w : W0 ⟶ W1)
    (hA : x ≫ A1.hom = A0.hom ≫ y)
    (hB : B0.hom ≫ z = y ≫ B1.hom) (hC : C0.hom ≫ w = z ≫ C1.hom) :
    (A0 ≪≫ B0 ≪≫ C0).hom ≫ w = x ≫ (A1 ≪≫ B1 ≪≫ C1).hom := by
  simp only [Iso.trans_hom]
  calc
    (A0.hom ≫ B0.hom ≫ C0.hom) ≫ w =
      A0.hom ≫ B0.hom ≫ (C0.hom ≫ w) := by simp only [Category.assoc]
    _ = A0.hom ≫ B0.hom ≫ (z ≫ C1.hom) := by rw [hC]
    _ = A0.hom ≫ (B0.hom ≫ z) ≫ C1.hom := by simp only [Category.assoc]
    _ = A0.hom ≫ (y ≫ B1.hom) ≫ C1.hom := by rw [hB]
    _ = (A0.hom ≫ y) ≫ (B1.hom ≫ C1.hom) := by simp only [Category.assoc]
    _ = (x ≫ A1.hom) ≫ (B1.hom ≫ C1.hom) := by rw [hA]
    _ = x ≫ (A1.hom ≫ B1.hom ≫ C1.hom) := by simp only [Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
