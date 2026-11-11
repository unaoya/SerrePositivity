module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomTransport

/-! # 対象・次数の等式付き異種等号の代数則

概要：端点と次数を等式で指定すると、異種等号は微分・線形演算・合成を保つ。
方針：等式を消去して同じ Hom の通常の等号へ戻す。
規約：HA Construction 1.3.1.6。使われ方：境界の生の残差恒等式を型付き Hom 座標へ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：端点・次数に沿う移送は元の射との異種等号の証明も同時に与える。
方針：既存の線形移送とその異種等号を部分型にまとめる。
規約：HA Construction 1.3.1.6。使われ方：具体的な境界で移送の証明を再計算せず取り出す。 -/
def gradedHomTransportWithHEq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) (f : GradedHom A x y k) :
    {g : GradedHom A x' y' l // HEq g f} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport hx hy hk f, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq hx hy hk f⟩

/-- 概要：端点・次数の等式を伴う二射の異種等号は微分を保つ。
方針：等式を消去し、同じ微分に通常の等号を適用する。
規約：HA Construction 1.3.1.6。使われ方：移送後の残差の微分の比較。 -/
lemma gradedHom_differential_heq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l)
    (f : GradedHom A x y k) (g : GradedHom A x' y' l) (hfg : HEq f g) :
    HEq (differential A f) (differential A g) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq hfg
  rfl

/-- 概要：端点・次数の等式を伴う異種等号は負を保つ。
方針：等式を消去して負に通常の等号を適用する。
規約：HA Construction 1.3.1.6。使われ方：残差の負号を Hom 座標へ移す。 -/
lemma gradedHom_neg_heq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l)
    (f : GradedHom A x y k) (g : GradedHom A x' y' l) (hfg : HEq f g) :
    HEq (-f) (-g) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq hfg
  rfl

/-- 概要：同じ端点・次数の等式を伴う二つの異種等号は和を保つ。
方針：等式を消去して二つの通常の等号を使う。
規約：HA Construction 1.3.1.6。使われ方：三角形の残差の和を Hom 座標へ移す。 -/
lemma gradedHom_add_heq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l)
    (f₁ f₂ : GradedHom A x y k) (g₁ g₂ : GradedHom A x' y' l)
    (h₁ : HEq f₁ g₁) (h₂ : HEq f₂ g₂) : HEq (f₁ + f₂) (g₁ + g₂) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq h₁
  cases eq_of_heq h₂
  rfl

/-- 概要：同じ端点・次数の等式を伴う二つの異種等号は差を保つ。
方針：等式を消去して二つの通常の等号を使う。
規約：HA Construction 1.3.1.6。使われ方：三角形の残差の差を Hom 座標へ移す。 -/
lemma gradedHom_sub_heq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l)
    (f₁ f₂ : GradedHom A x y k) (g₁ g₂ : GradedHom A x' y' l)
    (h₁ : HEq f₁ g₁) (h₂ : HEq f₂ g₂) : HEq (f₁ - f₂) (g₁ - g₂) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq h₁
  cases eq_of_heq h₂
  rfl

/-- 概要：端点・次数の等式を伴う二つの異種等号は通常順の合成を保つ。
方針：三対象と三次数の等式を消去し、入力二射の通常の等号と証明の一意性を使う。
規約：HA Construction 1.3.1.6。使われ方：脚と高次成分との合成を標準 fiber の成分へ移す。 -/
lemma gradedHom_compose_heq {x y z x' y' z' : D} {p q k p' q' k' : ℤ}
    (hx : x = x') (hy : y = y') (hz : z = z') (hp : p = p') (hq : q = q') (hk : k = k')
    (g : GradedHom A y z q) (f : GradedHom A x y p)
    (g' : GradedHom A y' z' q') (f' : GradedHom A x' y' p')
    (hg : HEq g g') (hf : HEq f f') (h : p + q = k) (h' : p' + q' = k') :
    HEq (compose A g f h) (compose A g' f' h') := by
  cases hx
  cases hy
  cases hz
  cases hp
  cases hq
  cases hk
  cases eq_of_heq hg
  cases eq_of_heq hf
  rfl

/-- 概要：端点・次数が等式で一致する二つの Hom の零元は異種等号で一致する。
方針：三つの等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：未知成分と右側の零ホモトピーを比較する。 -/
lemma gradedHom_zero_heq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) :
    HEq (0 : GradedHom A x y k) (0 : GradedHom A x' y' l) := by
  cases hx
  cases hy
  cases hk
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
