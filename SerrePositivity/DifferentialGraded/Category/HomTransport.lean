module
public import SerrePositivity.DifferentialGraded.Category.Basic
/-!
概要：Hom 複体の同型に沿って dg 圏の単位・合成・三法則を移す。
方針：全 Hom の指定同型で合成を共役し、元の三法則を単射性で反映する。
規約：対象ラベルを保持し、既存の dg 圏を変更しない。
使われ方：係数閉包の各 Hom を固定自由加群の商による提示へ符号化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (H : D → D → Complex R) (e : ∀ x y, H x y ≅ homObject R D x y)

lemma dgHomTransport_left (x y : D) :
    (λ_ (H x y)).inv ≫ (eId (Complex R) x ≫ (e x x).inv) ▷ H x y ≫
      ((e x x).hom ⊗ₘ (e x y).hom) ≫ eComp (Complex R) x x y ≫ (e x y).inv = 𝟙 _ := by
  apply (cancel_mono (e x y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [whiskerRight_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, Category.assoc, Category.comp_id]
  rw [leftUnitor_inv_comp_tensorHom_assoc, e_id_comp]
  simp

lemma dgHomTransport_right (x y : D) :
    (ρ_ (H x y)).inv ≫ H x y ◁ (eId (Complex R) y ≫ (e y y).inv) ≫
      ((e x y).hom ⊗ₘ (e y y).hom) ≫ eComp (Complex R) x y y ≫ (e x y).inv = 𝟙 _ := by
  apply (cancel_mono (e x y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [whiskerLeft_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, Category.assoc, Category.comp_id]
  rw [rightUnitor_inv_comp_tensorHom_assoc, e_comp_id]
  simp

lemma dgHomTransport_assoc (w x y z : D) :
    (α_ (H w x) (H x y) (H y z)).inv ≫
      (((e w x).hom ⊗ₘ (e x y).hom) ≫ eComp (Complex R) w x y ≫ (e w y).inv) ▷ H y z ≫
      ((e w y).hom ⊗ₘ (e y z).hom) ≫ eComp (Complex R) w y z ≫ (e w z).inv =
    H w x ◁ (((e x y).hom ⊗ₘ (e y z).hom) ≫
      eComp (Complex R) x y z ≫ (e x z).inv) ≫
      ((e w x).hom ⊗ₘ (e x z).hom) ≫ eComp (Complex R) w x z ≫ (e w z).inv := by
  apply (cancel_mono (e w z).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  rw [← tensorHom_comp_whiskerRight_assoc, ← associator_inv_naturality_assoc, e_assoc]
  rw [← tensorHom_comp_whiskerLeft_assoc]

@[instance_reducible] def dgCategoryHomTransport : DGCategory R D :=
  ofHomObjects R D H
    (fun x => eId (Complex R) x ≫ (e x x).inv)
    (fun x y z => ((e x y).hom ⊗ₘ (e y z).hom) ≫
      eComp (Complex R) x y z ≫ (e x z).inv)
    (dgHomTransport_left R D H e) (dgHomTransport_right R D H e)
    (dgHomTransport_assoc R D H e)

end SerrePositivity.DifferentialGraded
