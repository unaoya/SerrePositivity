module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.IsoThreeStepSquare
/-!
概要：元の kernel 合成子の右変数自然性を、同じ通常比較と raw 経路で照合する。
方針：元の指定比較と射の値を保持し、全関手圏の実作用と可換四角形を使う。
規約：後続 kernel の平坦性・射の可逆性は要求しない。使われ方：模型変更の整合性。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
lemma iso_conjugation_hom_square {C : Type*} [Category C]
    {X0 X1 Y0 Y1 : C} (r0 : X0 ≅ Y0) (r1 : X1 ≅ Y1)
    (a : X0 ⟶ X1) (b : Y0 ⟶ Y1) (ha : a = r0.hom ≫ b ≫ r1.inv) :
    r0.hom ≫ b = a ≫ r1.hom := by
  rw [ha]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
lemma iso_square_of_raw_factor_paths {C : Type*} [Category C]
    {X0 X1 Y0 Y1 Z0 Z1 : C} (k0 : X0 ≅ Y0) (k1 : X1 ≅ Y1)
    (r0 : Y0 ≅ Z0) (r1 : Y1 ≅ Z1) (p0 : X0 ⟶ Z0) (p1 : X1 ⟶ Z1)
    (x : X0 ⟶ X1) (y : Y0 ⟶ Y1) (z : Z0 ⟶ Z1)
    (h0 : k0.hom ≫ r0.hom = p0) (h1 : k1.hom ≫ r1.hom = p1)
    (hr : r0.hom ≫ z = y ≫ r1.hom) (hp : p0 ≫ z = x ≫ p1) :
    k0.hom ≫ y = x ≫ k1.hom := by
  apply (cancel_mono r1.hom).1
  calc
    (k0.hom ≫ y) ≫ r1.hom = k0.hom ≫ (y ≫ r1.hom) := Category.assoc _ _ _
    _ = k0.hom ≫ (r0.hom ≫ z) := congrArg (fun t => k0.hom ≫ t) hr.symm
    _ = (k0.hom ≫ r0.hom) ≫ z := (Category.assoc _ _ _).symm
    _ = p0 ≫ z := congrArg (fun t => t ≫ z) h0
    _ = x ≫ p1 := hp
    _ = x ≫ (k1.hom ≫ r1.hom) := congrArg (fun t => x ≫ t) h1.symm
    _ = (x ≫ k1.hom) ≫ r1.hom := (Category.assoc _ _ _).symm
lemma iso_compositor_square_of_three_step_raw {T : Type*} [Category T]
    {X0 X1 Y0 Y1 Z0 Z1 W0 W1 V0 V1 : T}
    (k0 : X0 ≅ V0) (k1 : X1 ≅ V1) (r0 : V0 ≅ W0) (r1 : V1 ≅ W1)
    (A0 : X0 ≅ Y0) (A1 : X1 ≅ Y1) (B0 : Y0 ≅ Z0) (B1 : Y1 ≅ Z1)
    (C0 : Z0 ≅ W0) (C1 : Z1 ≅ W1)
    (x : X0 ⟶ X1) (y : Y0 ⟶ Y1) (z : Z0 ⟶ Z1) (w : W0 ⟶ W1) (t : V0 ⟶ V1)
    (h0 : k0.hom ≫ r0.hom = A0.hom ≫ B0.hom ≫ C0.hom)
    (h1 : k1.hom ≫ r1.hom = A1.hom ≫ B1.hom ≫ C1.hom)
    (hA : x ≫ A1.hom = A0.hom ≫ y)
    (hB : B0.hom ≫ z = y ≫ B1.hom) (hC : C0.hom ≫ w = z ≫ C1.hom)
    (hr : r0.hom ≫ w = t ≫ r1.hom) : k0.hom ≫ t = x ≫ k1.hom := by
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_three_step_square A0 A1 B0 B1 C0 C1 x y z w hA hB hC
  exact iso_square_of_raw_factor_paths k0 k1 r0 r1
    (A0 ≪≫ B0 ≪≫ C0).hom (A1 ≪≫ B1 ≪≫ C1).hom x t w h0 h1 hr hp
end SerrePositivity.InfinityCategories.Project.DerivedCategories
