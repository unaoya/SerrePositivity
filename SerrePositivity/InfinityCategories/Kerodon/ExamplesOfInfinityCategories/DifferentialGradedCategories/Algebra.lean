module
public import SerrePositivity.DifferentialGraded.Category.Basic

/-! # dg nerve の成分計算に使う合成の法則

概要：通常順の斉次合成の零・単位・各変数の加法性と符号スカラーの法則を与える。
方針：tensor の零と豊穣合成の線形性を使う。
規約：HA Construction 1.3.1.6、通常順は `compose A g f h`。
使われ方：退化単体の方程式の合成項の消去と、ホーン充填の残差の展開。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

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

/-- 概要：通常順合成は後に作用する射の加法を保つ。
方針：tensor と豊穣合成の線形性。
規約：HA Proposition 1.3.1.10。使われ方：残差恒等式の合成項の展開。 -/
lemma compose_add_left {x y z : D} {p q k : ℤ}
    (g g' : GradedHom A y z q) (f : GradedHom A x y p) (h : p + q = k) :
    compose A (g + g') f h = compose A g f h + compose A g' f h := by
  simp [compose, forward, TensorProduct.tmul_add, smul_add]

/-- 概要：通常順合成は先に作用する射の加法を保つ。
方針：tensor と豊穣合成の線形性。
規約：HA Proposition 1.3.1.10。使われ方：残差恒等式の合成項の展開。 -/
lemma compose_add_right {x y z : D} {p q k : ℤ}
    (g : GradedHom A y z q) (f f' : GradedHom A x y p) (h : p + q = k) :
    compose A g (f + f') h = compose A g f h + compose A g f' h := by
  simp [compose, forward, TensorProduct.add_tmul, smul_add]

/-- 概要：通常順合成は後に作用する射の差を保つ。
方針：tensor と豊穣合成の線形性。
規約：HA Proposition 1.3.1.10。使われ方：微分と右辺の差の展開。 -/
lemma compose_sub_left {x y z : D} {p q k : ℤ}
    (g g' : GradedHom A y z q) (f : GradedHom A x y p) (h : p + q = k) :
    compose A (g - g') f h = compose A g f h - compose A g' f h := by
  simp [compose, forward, TensorProduct.tmul_sub, smul_sub]

/-- 概要：通常順合成は先に作用する射の差を保つ。
方針：tensor と豊穣合成の線形性。
規約：HA Proposition 1.3.1.10。使われ方：微分と右辺の差の展開。 -/
lemma compose_sub_right {x y z : D} {p q k : ℤ}
    (g : GradedHom A y z q) (f f' : GradedHom A x y p) (h : p + q = k) :
    compose A g (f - f') h = compose A g f h - compose A g f' h := by
  simp [compose, forward, TensorProduct.sub_tmul, smul_sub]

/-- 概要：通常順合成は後に作用する射の符号スカラーを外へ出せる。
方針：整数スカラーと tensor の両立および線形性。
規約：HA Proposition 1.3.1.10。使われ方：二重切断の符号の整理。 -/
lemma compose_units_smul_left {x y z : D} {p q k : ℤ} (c : ℤˣ)
    (g : GradedHom A y z q) (f : GradedHom A x y p) (h : p + q = k) :
    compose A (c • g) f h = c • compose A g f h := by
  simp only [compose, forward, Units.smul_def, TensorProduct.tmul_smul, map_zsmul]
  exact smul_comm _ _ _

/-- 概要：通常順合成は先に作用する射の符号スカラーを外へ出せる。
方針：整数スカラーと tensor の両立および線形性。
規約：HA Proposition 1.3.1.10。使われ方：二重切断の符号の整理。 -/
lemma compose_units_smul_right {x y z : D} {p q k : ℤ} (c : ℤˣ)
    (g : GradedHom A y z q) (f : GradedHom A x y p) (h : p + q = k) :
    compose A g (c • f) h = c • compose A g f h := by
  simp only [compose, forward, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]
  exact smul_comm _ _ _

/-- 概要：通常順合成は後に作用する射の有限和を保つ。
方針：tensor と豊穣合成の線形性および符号スカラーの有限和への分配を使う。
規約：HA Proposition 1.3.1.10。使われ方：切断成分の境界の合成を二重和へ展開する。 -/
lemma compose_sum_left {ι : Type*} {x y z : D} {p q k : ℤ}
    (S : Finset ι) (g : ι → GradedHom A y z q) (f : GradedHom A x y p) (h : p + q = k) :
    compose A (∑ i ∈ S, g i) f h = ∑ i ∈ S, compose A (g i) f h := by
  simp [compose, forward, TensorProduct.tmul_sum, Finset.smul_sum]

/-- 概要：通常順合成は先に作用する射の有限和を保つ。
方針：tensor と豊穣合成の線形性および符号スカラーの有限和への分配を使う。
規約：HA Proposition 1.3.1.10。使われ方：切断成分の境界の合成を二重和へ展開する。 -/
lemma compose_sum_right {ι : Type*} {x y z : D} {p q k : ℤ}
    (S : Finset ι) (g : GradedHom A y z q) (f : ι → GradedHom A x y p) (h : p + q = k) :
    compose A g (∑ i ∈ S, f i) h = ∑ i ∈ S, compose A g (f i) h := by
  simp [compose, forward, TensorProduct.sum_tmul, Finset.smul_sum]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
