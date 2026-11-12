module
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
/-!
概要：三角整合性を満たす同値の余単位は、adjointify の補正によって変わらない。
方針：実 fiber の射影の恒等性と、指定二比較の前後合成を照合する。
規約：元の指定射と同型を保持する。使われ方：入力分解の同じ余単位の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory Bicategory

/-- 左三角式を既に満たす余単位は、adjointify の補正で厳密に変わらない。 -/
lemma bicategoryAdjointifyCounit_eq_of_left_triangle
    {T : Type u} [Bicategory.{w, v} T] {a b : T} {f : a ⟶ b} {g : b ⟶ a}
    (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
    (h : leftZigzagIso η ε = (λ_ f) ≪≫ (ρ_ f).symm) :
    adjointifyCounit η ε = ε := by
  unfold adjointifyCounit
  rw [← leftZigzagIso_symm, h]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]
  apply Iso.ext
  change (g ◁ 𝟙 f) ≫ ε.hom = ε.hom
  rw [whiskerLeft_id, Category.id_comp]
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
