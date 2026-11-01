module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ExtOne
public import SerrePositivity.InfinityCategories.Core.Join

/-!
# Thin 圏の nerve への全写像の頂点判定

概要：通常の thin 圏を標的とする写像は全頂点での値で決まる。
方針：元の strict Segal 一次判定に端点と Hom の一意性を渡す。
規約：始域は任意の単体集合を許す。
使われ方：有限終点拡張の通常余錐表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

lemma thinNerve_hom_ext_zero {K : SSet.{u}} {C : Type u}
    [Category.{u} C] [Quiver.IsThin C] {f g : K ⟶ nerve C}
    (h : ∀ s : K _⦋0⦌, f.app _ s = g.app _ s) : f = g := by
  apply SerrePositivity.InfinityCategories.F1B.nerve_hom_ext_one
  intro s
  have h₀ := congrArg (fun F : (nerve C) _⦋0⦌ => F.obj 0) (h (K.δ 1 s))
  have h₁ := congrArg (fun F : (nerve C) _⦋0⦌ => F.obj 0) (h (K.δ 0 s))
  change (f.app _ (K.map (SimplexCategory.δ 1).op s)).obj 0 =
    (g.app _ (K.map (SimplexCategory.δ 1).op s)).obj 0 at h₀
  change (f.app _ (K.map (SimplexCategory.δ 0).op s)).obj 0 =
    (g.app _ (K.map (SimplexCategory.δ 0).op s)).obj 0 at h₁
  rw [f.naturality_apply, g.naturality_apply] at h₀ h₁
  apply ComposableArrows.ext₁ h₀ h₁
  exact Subsingleton.elim _ _

lemma thinNerve_join_hom_ext {K L : SSet.{u}} {C : Type u}
    [Category.{u} C] [Quiver.IsThin C] {f g : join K L ⟶ nerve C}
    (hL : joinInl K L ≫ f = joinInl K L ≫ g)
    (hR : joinInr K L ≫ f = joinInr K L ≫ g) : f = g := by
  apply thinNerve_hom_ext_zero
  rintro ⟨l, a, b⟩
  fin_cases l
  · cases a
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hR (Opposite.op ⦋0⦌)) b
  · cases b
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hL (Opposite.op ⦋0⦌)) a

end SerrePositivity.EInfinity.FrameHom
