module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanOneTailBianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanPrefixBianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle

/-! # cospan の先頭と脚の右辺の座標

概要：未知成分の方程式の右辺と残差を固定した端点・次数で評価する。
方針：先頭集合と末尾一点追加集合の端点と濃度の公式を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の有限残差系の座標表示。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：先頭の未知成分を零番目の頂点から錐頂点への次数 −n の射として評価する。
方針：先頭集合の端点と n+2 という濃度を用いる。
規約：HA Proposition 1.3.1.10。使われ方：有限残差系の未知成分 a。 -/
def cospanPrefixHom {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    GradedHom A (s.obj 0) (s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)) (-(n : ℤ)) :=
  s.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospanPrefixHom)


/-- 概要：先頭の未知成分の方程式の右辺を固定した次数で評価する。
方針：先頭の濃度と端点を右辺の引数に指定する。
規約：HA Proposition 1.3.1.10。使われ方：有限残差系の r₀。 -/
def cospanPrefixRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    GradedHom A (s.obj 0) (s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)) (-(n : ℤ) + 1) :=
  s.rhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospanPrefixRhs)


/-- 概要：先頭の方程式の残差を固定した次数で評価する。
方針：微分と右辺の差という既存の残差を同じ引数で評価する。
規約：HA Proposition 1.3.1.10。使われ方：脚の Bianchi に残る先頭の残差。 -/
def cospanPrefixResidual {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    GradedHom A (s.obj 0) (s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)) (-(n : ℤ) + 1) :=
  s.residual (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospanPrefixResidual)


/-- 概要：末尾一点を加えた方程式の右辺を零番目の頂点からその点への射として評価する。
方針：追加後の n+3 という濃度と最大元の公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：有限残差系の脚側の右辺。 -/
def cospanOneTailRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) :
    GradedHom A (s.obj 0) (s.obj b) (-(n : ℤ) - 1 + 1) :=
  s.rhs (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 b (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert b hb]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_min b _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_max b hb _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert b hb]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospanOneTailRhs)


/-- 概要：先頭の座標の残差は未知成分の微分と右辺の差。
方針：三つの座標と残差の定義を展開する。
規約：HA Proposition 1.3.1.10。使われ方：未知成分を零と置いたときの符号の計算。 -/
lemma cospanPrefixResidual_eq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    s.cospanPrefixResidual = differential A s.cospanPrefixHom - s.cospanPrefixRhs := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospanPrefixResidual_eq)


/-- 概要：既知方程式を満たすデータでは先頭の右辺の座標は閉じている。
方針：先頭集合の Bianchi の閉性に固定した端点と次数を代入する。
規約：HA Proposition 1.3.1.10。使われ方：残差系の δr₀=0。 -/
lemma cospanPrefixRhs_closed {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I → s.Equation I) :
    differential A s.cospanPrefixRhs = 0 :=
  s.differential_rhs_cospanPrefix hknown _ _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospanPrefixRhs_closed)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
