module
public import SerrePositivity.DifferentialGraded.Category.Tensor
/-!
概要：端点・次数の等式と成分の異種等号を、同じ斉次 tensor 要素へ移す。
方針：二つの端点と三次数の等式を消去し、同じ二つの実成分に戻す。
規約：次数合わせは明示した等式を使う。使われ方：tensor 候補の成分比較と自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 同じ端点・次数を持つ二成分の異種等号は、同じ実 tensor 要素を保つ。 -/
lemma dgTensorElement_heq {x y x' y' : DGTensorCategory R B C}
    {p q n p' q' n' : ℤ} (hx : x = x') (hy : y = y')
    (hp : p = p') (hq : q = q') (hn : n = n')
    (f : GradedHom R x.1 y.1 p) (g : GradedHom R x.2 y.2 q)
    (f' : GradedHom R x'.1 y'.1 p') (g' : GradedHom R x'.2 y'.2 q')
    (hf : HEq f f') (hg : HEq g g') (h : p + q = n) (h' : p' + q' = n') :
    HEq (dgTensorElement R f g h) (dgTensorElement R f' g' h') := by
  cases hx
  cases hy
  cases hp
  cases hq
  cases hn
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
