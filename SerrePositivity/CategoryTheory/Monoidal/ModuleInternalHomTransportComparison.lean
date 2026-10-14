module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomTransport

/-! # 内部Homの作用の移送を二つの比較同型で計算する -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] (M : C) [MonObj M] [IsCommMonObj M] [HasEqualizers C]
  (X : C) (F : Mod C M) {Y Z : C} (e : (ihom X).obj F.X ≅ Y) (d : Y ≅ Z)

/-- 比較の合成による移送を、最初の移送済み加群との同型として表示する。 -/
def furtherTransportedIso : transportedObj M X F e ≅ transportedObj M X F (e ≪≫ d) :=
  (transportedIso M X F e).symm ≪≫ transportedIso M X F (e ≪≫ d)

/-- 二段目の加群比較の基礎射は二段目の比較の順射。 -/
lemma furtherTransportedIso_hom :
    (furtherTransportedIso M X F e d).hom.hom = d.hom := by
  change e.inv ≫ (e.hom ≫ d.hom) = d.hom
  simp only [Iso.inv_hom_id_assoc]

/-- 二段目の加群比較の逆基礎射は二段目の比較の逆射。 -/
lemma furtherTransportedIso_inv :
    (furtherTransportedIso M X F e d).inv.hom = d.inv := by
  change (d.inv ≫ e.inv) ≫ e.hom = d.inv
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.MonoidalModuleInternalHom
