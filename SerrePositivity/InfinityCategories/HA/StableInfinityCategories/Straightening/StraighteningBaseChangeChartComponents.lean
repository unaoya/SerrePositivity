module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Iso

/-!
分割で生成：docstring を書き直すこと
 # 元の左右の底変換比較は、それぞれ同じ初頂点切断比較の指定成分
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening
open _root_.SerrePositivity.KST.Fibration

lemma prependEq_heq {C : Type v} [Category.{w} C] {a a' b : C}
    (h : a = a') (e : a' ≅ b) : HEq (eqToIso h ≪≫ e) e := by
  subst a'
  simp only [eqToIso_refl, Iso.refl_trans]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.prependEq_heq := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.prependEq_heq
