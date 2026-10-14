module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # 作用の単位比較を随伴の右随伴へ送る -/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.ActionUnitAdjunction

open CategoryTheory

variable {C : Type u} [Category.{v} C] {L R : C ⥤ C}
  (a : L ⊣ R) (e : L ≅ 𝟭 C)

/-- 左随伴の単位比較から得る右随伴の単位比較。 -/
def rightUnitIso : R ≅ 𝟭 C := (a.ofNatIsoLeft e).rightAdjointUniq Adjunction.id

/-- 右随伴の単位比較を元の評価で計算する。 -/
lemma rightUnitIso_hom (X : C) :
    (rightUnitIso a e).hom.app X = e.inv.app (R.obj X) ≫ a.counit.app X := by
  have h := (a.ofNatIsoLeft e).rightAdjointUniq_hom_app_counit Adjunction.id X
  change (rightUnitIso a e).hom.app X ≫ 𝟙 X =
    e.inv.app (R.obj X) ≫ a.counit.app X at h
  erw [Category.comp_id] at h
  exact h

end SerrePositivity.ActionUnitAdjunction
