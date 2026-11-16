module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：同じ合成の両端を同じ可逆射に合わせ、中央の射を元の恒等射へ戻す。
方針：Arrowの端点の等式を外して、同じ圏で左右の可逆射を相殺する。
規約：端点と元の射を保持する。
使われ方：元の補正単位の像の同じ三辺の合成則の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
noncomputable section

namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ二つの外側の射と合成の Arrow の一致から、中央の Arrow は元の恒等射になる。 -/
lemma arrow_middle_unit_of_outer_arrow_equalities {D : Type u} [Category.{v} D]
    {q x y z q₀ x₀ z₀ : D} (p : q ⟶ x) (a : x ⟶ y) (r : y ⟶ z) (b : q ⟶ z)
    (p₀ : q₀ ⟶ x₀) (r₀ : x₀ ⟶ z₀) [IsIso p] [IsIso r]
    (hp : Arrow.mk p = Arrow.mk p₀) (hr : Arrow.mk r = Arrow.mk r₀)
    (hb : Arrow.mk b = Arrow.mk (p₀ ≫ r₀)) (h : p ≫ a ≫ r = b) :
    Arrow.mk a = Arrow.mk (𝟙 x₀) := by
  obtain ⟨hq, hx, hp⟩ := (Arrow.mk_eq_mk_iff _ _).mp hp
  subst q x
  obtain ⟨hy, hz, hr⟩ := (Arrow.mk_eq_mk_iff _ _).mp hr
  subst y z
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hp hr
  subst p r
  have hb' : b = p₀ ≫ r₀ := (Arrow.mk_inj _ _).mp hb
  rw [hb'] at h
  suffices ha : a = 𝟙 x₀ by exact congrArg Arrow.mk ha
  apply (cancel_mono r₀).mp
  apply (cancel_epi p₀).mp
  simpa only [Category.assoc, Category.comp_id, Category.id_comp] using h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

end
