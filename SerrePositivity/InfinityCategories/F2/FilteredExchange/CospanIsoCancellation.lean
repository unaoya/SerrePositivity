module

public import Mathlib.CategoryTheory.Iso

/-!
概要：二つの指定三角形の整合式から共通の中心比較を消去する。
方針：同型の順方向の射の式と逆同型の単位則。
規約：外側の指定同型の値を保持。使われ方：native な二脚の可換性の比較。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：共通の中心同型を介する二つの整合式は二脚の可換性の整合式を与える。
方針：元の二式で置き換えて中心比較を消去。
規約：指定値の等式。使われ方：全空間錐と区間錐の可換性の比較。 -/
lemma cospanIso_cancel {C : Type u} [Category.{v} C] {W L R V TL TR : C}
    (l : W ≅ L) (r : W ≅ R) (el : L ≅ TL) (er : R ≅ TR)
    (e : W ≅ V) (vl : V ≅ TL) (vr : V ≅ TR)
    (hl : l ≪≫ el = e ≪≫ vl) (hr : r ≪≫ er = e ≪≫ vr) :
    l.symm ≪≫ r ≪≫ er = el ≪≫ vl.symm ≪≫ vr := by
  have hL := congrArg Iso.hom hl
  have hR := congrArg Iso.hom hr
  simp only [Iso.trans_hom] at hL hR
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    _ = l.inv ≫ e.hom ≫ vr.hom := by rw [hR]
    _ = l.inv ≫ (e.hom ≫ vl.hom) ≫ vl.inv ≫ vr.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = l.inv ≫ (l.hom ≫ el.hom) ≫ vl.inv ≫ vr.hom := by rw [← hL]
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2
