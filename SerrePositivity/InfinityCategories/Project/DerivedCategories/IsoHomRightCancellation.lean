module
public import Mathlib.CategoryTheory.Iso
/-!
概要：同じ augmentation の四角形を満たす模型射の導来像は選択によらない。
方針：元の出力模型比較を消去し、準同値への後合成の充満忠実性で反映する。
規約：指定比較を変更しない。使われ方：一般 cell 模型の選択整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
lemma iso_hom_right_cancel_typed {T : Type*} [Category T] {X Y Z : T}
    (d : Y ≅ Z) {f g : X ⟶ Y} (h : f ≫ d.hom = g ≫ d.hom) : f = g :=
  (cancel_mono d.hom).1 h
lemma iso_symm_eq_of_trans_eq_refl_typed {T : Type*} [Category T] {X Y : T}
    (e : X ≅ Y) (d : Y ≅ X) (h : d ≪≫ e = Iso.refl Y) : e.symm = d := by
  apply Iso.ext
  apply iso_hom_right_cancel_typed e
  have hm := congrArg (fun a : _ ≅ _ => a.hom) h
  simpa only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Iso.inv_hom_id] using! hm.symm
lemma iso_eq_trans_symm_of_hom_square {T : Type*} [Category T] {X Y Z : T}
    (e : X ≅ Y) (a : X ≅ Z) (b : Y ≅ Z) (h : a.hom = e.hom ≫ b.hom) :
    e = a ≪≫ b.symm := by
  apply Iso.ext
  exact (Iso.eq_comp_inv b).2 h.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
