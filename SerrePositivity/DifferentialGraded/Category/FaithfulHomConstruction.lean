module
public import SerrePositivity.DifferentialGraded.Category.Basic
/-!
概要：単位・合成と両立する単射 Hom 比較から dg 圏の三法則を反映する。
方針：各法則を忠実な Hom 鎖写像で後合成し、元の豊穣圏の法則へ帰着する。
規約：比較写像の同型性は要求せず、構造射の両立を明示入力とする。
使われ方：c′ の微分・合成で閉じた係数 submodule 族から実 dg 圏を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (H : D → D → Complex R) (ι : ∀ x y, H x y ⟶ homObject R D x y)
  [∀ x y, Mono (ι x y)] (unit : ∀ x, 𝟙_ (Complex R) ⟶ H x x)
  (comp : ∀ x y z, H x y ⊗ H y z ⟶ H x z)
  (hu : ∀ x, unit x ≫ ι x x = eId (Complex R) x)
  (hc : ∀ x y z, comp x y z ≫ ι x z =
    (ι x y ⊗ₘ ι y z) ≫ eComp (Complex R) x y z)

include ι hu hc in
lemma dgFaithfulHom_left (x y : D) :
    (λ_ (H x y)).inv ≫ unit x ▷ H x y ≫ comp x x y = 𝟙 _ := by
  apply (cancel_mono (ι x y)).1
  simp only [Category.assoc, hc, Category.id_comp]
  rw [whiskerRight_comp_tensorHom_assoc, hu,
    leftUnitor_inv_comp_tensorHom_assoc, e_id_comp]
  simp

include ι hu hc in
lemma dgFaithfulHom_right (x y : D) :
    (ρ_ (H x y)).inv ≫ H x y ◁ unit y ≫ comp x y y = 𝟙 _ := by
  apply (cancel_mono (ι x y)).1
  simp only [Category.assoc, hc, Category.id_comp]
  rw [whiskerLeft_comp_tensorHom_assoc, hu,
    rightUnitor_inv_comp_tensorHom_assoc, e_comp_id]
  simp

include ι hc in
lemma dgFaithfulHom_assoc (w x y z : D) :
    (α_ (H w x) (H x y) (H y z)).inv ≫ comp w x y ▷ H y z ≫ comp w y z =
      H w x ◁ comp x y z ≫ comp w x z := by
  apply (cancel_mono (ι w z)).1
  simp only [Category.assoc, hc, whiskerRight_comp_tensorHom_assoc,
    whiskerLeft_comp_tensorHom_assoc]
  rw [← tensorHom_comp_whiskerRight_assoc, ← associator_inv_naturality_assoc, e_assoc]
  rw [← tensorHom_comp_whiskerLeft_assoc]

@[instance_reducible] def dgCategoryOfFaithfulHomMaps : DGCategory R D :=
  ofHomObjects R D H unit comp
    (dgFaithfulHom_left R D H ι unit comp hu hc)
    (dgFaithfulHom_right R D H ι unit comp hu hc)
    (dgFaithfulHom_assoc R D H ι comp hc)

end SerrePositivity.DifferentialGraded
