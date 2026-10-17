module
public import SerrePositivity.DifferentialGraded.Category.Components

/-! # dg nerve の成分計算に使う零の法則

概要：通常順の斉次合成はどちらかの入力が零なら零。
方針：tensor の零と豊穣合成の線形性を使う。
規約：HA Construction 1.3.1.6、通常順は `compose A g f h`。
使われ方：退化単体の方程式の零となる合成項を除く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：先に作用する斉次射が零なら合成は零。
方針：純粋 tensor の零と線形写像の零の保存。
規約：HA Construction 1.3.1.6。使われ方：退化の合成項の消去。 -/
lemma compose_zero {x y z : D} {p q k : ℤ} (g : GradedHom A y z q) (h : p + q = k) :
    compose A g (0 : GradedHom A x y p) h = 0 := by
  simp [compose, forward]

/-- 概要：後に作用する斉次射が零なら合成は零。
方針：純粋 tensor の零と線形写像の零の保存。
規約：HA Construction 1.3.1.6。使われ方：退化の合成項の消去。 -/
lemma zero_compose {x y z : D} {p q k : ℤ} (f : GradedHom A x y p) (h : p + q = k) :
    compose A (0 : GradedHom A y z q) f h = 0 := by
  simp [compose, forward]

/-- 概要：次数と始点を等式で移送した単位との合成は元の射と異種等号で一致する。
方針：対象と次数の等式を消去し、既存の左単位則に帰着する。
規約：HA Construction 1.3.1.6。使われ方：始点に接する退化の合成項。 -/
lemma compose_unit_of_heq {x y z : D} {p q k : ℤ}
    (g : GradedHom A y z q) (f : GradedHom A x y p) (hn : p + q = k)
    (hxy : x = y) (hp : p = 0) (hf : HEq f (unitElement A y).val) :
    HEq (compose A g f hn) g := by
  cases hxy
  subst hp
  have hf' : f = (unitElement A x).val := eq_of_heq hf
  subst f
  have hk : k = q := by omega
  subst hk
  exact heq_of_eq (compose_unit A g)

/-- 概要：次数と終点を等式で移送した単位との合成は元の射と異種等号で一致する。
方針：対象と次数の等式を消去し、既存の右単位則に帰着する。
規約：HA Construction 1.3.1.6。使われ方：終点に接する退化の合成項。 -/
lemma unit_compose_of_heq {x y z : D} {p q k : ℤ}
    (g : GradedHom A y z q) (f : GradedHom A x y p) (hn : p + q = k)
    (hyz : y = z) (hq : q = 0) (hg : HEq g (unitElement A z).val) :
    HEq (compose A g f hn) f := by
  cases hyz
  subst hq
  have hg' : g = (unitElement A y).val := eq_of_heq hg
  subst g
  have hk : k = p := by omega
  subst hk
  exact heq_of_eq (unit_compose A f)

end SerrePositivity.InfinityCategories.DGNerve
