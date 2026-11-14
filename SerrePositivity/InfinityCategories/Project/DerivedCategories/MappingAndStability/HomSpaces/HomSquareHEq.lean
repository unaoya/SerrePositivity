module
public import Mathlib.CategoryTheory.Category.Basic
/-!
概要：元の全 Hom 正方形を同じ端点の厳密 dg 自然変換へ反映する。
方針：対象と実射の異種等式によって、抽象的な正方形の一致を移送する。
規約：同じ実作用と指定成分を保つ。使われ方：模型変更の比較同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
lemma hom_square_of_heq {T : Type u} [Category.{v} T]
    {K B C D B' C' D' : T} (hB : B = B') (hC : C = C') (hD : D = D')
    (p : K ⟶ B) (q : K ⟶ C) (a : B ⟶ D) (b : C ⟶ D)
    (p' : K ⟶ B') (q' : K ⟶ C') (a' : B' ⟶ D') (b' : C' ⟶ D')
    (hp : HEq p p') (hq : HEq q q') (ha : HEq a a') (hb : HEq b b')
    (h : p' ≫ a' = q' ≫ b') : p ≫ a = q ≫ b := by
  subst B' C' D'
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq ha
  cases eq_of_heq hb
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
