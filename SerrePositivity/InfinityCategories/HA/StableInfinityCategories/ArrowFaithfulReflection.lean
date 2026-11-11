module
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # 忠実かつ対象で単射な関手による Arrow 等式の反映

概要：端点の表示の違いを含む射の等式を、包含後の Arrow 等式から反映する。
方針：左右の射影で対象の等式を取り戻し、忠実性を同じ Hom に適用する。
規約：任意の圏。使われ方：D7 の Semifree の比較射の成分。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory
variable {C : Type u} [Category C] {D : Type v} [Category D]

/-- 対象で単射な忠実関手は、端点表示を含む Arrow 等式を反映する。 -/
lemma arrowMk_eq_of_faithful_map (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : Arrow.mk (F.map f) = Arrow.mk (F.map g)) : Arrow.mk f = Arrow.mk g := by
  have hx : X = X' := hF (congrArg Arrow.left h)
  have hy : Y = Y' := hF (congrArg Arrow.right h)
  cases hx
  cases hy
  exact congrArg Arrow.mk (F.map_injective (Arrow.mk_injective _ _ h))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
