module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle

/-! # 三頂点の高次成分の評価

概要：任意次元の単体データの三点成分を次数 −1 の射として評価する。
方針：三つの頂点が狭義に増加することから端点と濃度を決める。
規約：HA Construction 1.3.1.6、Example 1.3.1.8。使われ方：cospan の脚の三角形の成分。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：三つの順序付けた頂点の成分は次数 −1 の射。
方針：三点集合の最小元と最大元および濃度を評価する。
規約：HA Example 1.3.1.8。使われ方：三角形成分を Bianchi の残差と合成する。 -/
def tripleHom {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (a b c : Fin (n + 1))
    (hab : a < b) (hbc : b < c) : GradedHom A (s.obj a) (s.obj c) (-1) :=
  s.hom {a, b, c} a c (-1)
    (by simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)])
    (by symm; exact (Finset.min'_eq_iff _ _ _).2 (by simp [hab.le, (hab.trans hbc).le]))
    (by symm; exact (Finset.max'_eq_iff _ _ _).2 (by simp [hbc.le, (hab.trans hbc).le]))
    (by simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)])

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (tripleHom)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
