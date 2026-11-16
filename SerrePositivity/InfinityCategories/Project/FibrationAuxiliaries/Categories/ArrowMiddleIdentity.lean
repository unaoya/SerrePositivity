module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：元の合成の左右が同じ恒等射のArrowなら、中央と全合成のArrowは一致する。
方針：同じ端点の等式を外し、元の左右の恒等射を簡約する。
規約：元の全射と端点を保持する。
使われ方：同じtwisted Homの元の辺の合成則。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
noncomputable section

namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の合成の左右のArrowが恒等射のArrowなら、中央と合成のArrowが一致する。 -/
lemma arrow_middle_eq_of_outer_identity_arrows {D : Type u} [Category.{v} D]
    {q x y z x₀ y₀ : D} (p : q ⟶ x) (a : x ⟶ y) (r : y ⟶ z) (b : q ⟶ z)
    (hp : Arrow.mk p = Arrow.mk (𝟙 x₀)) (hr : Arrow.mk r = Arrow.mk (𝟙 y₀))
    (h : p ≫ a ≫ r = b) : Arrow.mk a = Arrow.mk b := by
  obtain ⟨hq, hx, hp⟩ := (Arrow.mk_eq_mk_iff _ _).mp hp
  subst q x
  obtain ⟨hy, hz, hr⟩ := (Arrow.mk_eq_mk_iff _ _).mp hr
  subst y z
  simp only [eqToHom_refl, Category.comp_id] at hp hr
  subst p r
  exact congrArg Arrow.mk (by simpa only [Category.id_comp, Category.comp_id] using h)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

end
