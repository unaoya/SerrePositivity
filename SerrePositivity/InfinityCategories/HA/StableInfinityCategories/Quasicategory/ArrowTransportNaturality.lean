module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
分割で生成：docstring を書き直すこと
概要：端点込みの Arrow の等号を、指定した等号同型との可換式へ戻す。
方針：始点・終点の等号を消去し、固定端点の射の等号を回収する。
規約：任意の同型に置き換えない。使われ方：BF 模型の頂点表示と整数 π の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w z
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma hom_eq_eqToHom_of_arrow_identity {C : Type u} [Category.{v} C] {a b c : C}
    (f : a ⟶ b) (hab : a = b) (h : Arrow.mk f = Arrow.mk (𝟙 c)) :
    f = eqToHom hab := by
  subst b
  obtain ⟨ha, _, he⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  subst c
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using he

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
