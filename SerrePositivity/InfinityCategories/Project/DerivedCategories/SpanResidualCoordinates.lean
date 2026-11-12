module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanOnePrefixResidual
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanSuffixBianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle

/-! # span の後続と脚の右辺の座標

概要：未知成分の方程式の右辺と残差を固定した端点・次数で評価する。
方針：後続集合と固定一点追加集合の端点と濃度の公式を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：D7 の有限残差系の座標表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：後続の未知成分を余錐頂点から最後の頂点への次数 −n の射として評価する。
方針：後続集合の端点と n+2 という濃度を用いる。
規約：HA Proposition 1.3.1.10。使われ方：有限残差系の未知成分 a。 -/
def spanSuffixHom {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    GradedHom A (s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ)) :=
  s.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanSuffixHom)


/-- 概要：後続の未知成分の方程式の右辺を固定した次数で評価する。
方針：後続の濃度と端点を右辺の引数に指定する。
規約：HA Proposition 1.3.1.10。使われ方：有限残差系の r₀。 -/
def spanSuffixRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    GradedHom A (s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ) + 1) :=
  s.rhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanSuffixRhs)


/-- 概要：後続の方程式の残差を固定した次数で評価する。
方針：微分と右辺の差という既存の残差を同じ引数で評価する。
規約：HA Proposition 1.3.1.10。使われ方：脚の Bianchi に残る後続の残差。 -/
def spanSuffixResidual {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    GradedHom A (s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ) + 1) :=
  s.residual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanSuffixResidual)


/-- 概要：固定一点を加えた方程式の右辺を追加点から最後の頂点への射として評価する。
方針：追加後の n+3 という濃度と最大元の公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：有限残差系の脚側の右辺。 -/
def spanOnePrefixRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    GradedHom A (s.obj a) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 1 + 1) :=
  s.rhs (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) a (Fin.last (n + 3)) (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert a ha]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min a ha _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max a _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert a ha]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanOnePrefixRhs)


/-- 概要：後続の座標の残差は未知成分の微分と右辺の差。
方針：三つの座標と残差の定義を展開する。
規約：HA Proposition 1.3.1.10。使われ方：未知成分を零と置いたときの符号の計算。 -/
lemma spanSuffixResidual_eq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    s.spanSuffixResidual = differential A s.spanSuffixHom - s.spanSuffixRhs := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanSuffixResidual_eq)


/-- 概要：既知方程式を満たすデータでは後続の右辺の座標は閉じている。
方針：後続集合の Bianchi の閉性に固定した端点と次数を代入する。
規約：HA Proposition 1.3.1.10。使われ方：残差系の δr₀=0。 -/
lemma spanSuffixRhs_closed {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I) :
    differential A s.spanSuffixRhs = 0 :=
  s.differential_rhs_spanSuffix hknown _ _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanSuffixRhs_closed)


/-- 概要：固定次数の脚側右辺の微分は後続残差と脚の符号付き合成の負。
方針：脚側 Bianchi に濃度と端点を代入し、次数の等式で座標に合わせる。
規約：符号は (-1)^(n+1)。使われ方：cofiber Hom 座標の整合条件。 -/
lemma spanOnePrefixRhs_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    differential A (s.spanOnePrefixRhs a ha) =
      -(((n : ℤ) + 1).negOnePow •
        compose A s.spanSuffixResidual (s.edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) (by omega)) := by
  dsimp only [spanOnePrefixRhs]
  rw [s.differential_rhs_span_onePrefix hknown a ha]
  dsimp only [spanSuffixResidual]
  congr 3
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces, Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | (simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces, Nat.cast_add, Nat.cast_ofNat]; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanOnePrefixRhs_differential)


/-- 概要：後続の未知成分が零なら脚側右辺の微分は後続右辺と脚の符号付き合成。
方針：残差を右辺の負に書き換え、二つの負号を相殺する。
規約：符号は (-1)^(n+1)。使われ方：実際の境界からの閉じた残差系。 -/
lemma spanOnePrefixRhs_differential_of_suffix_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (hzero : s.spanSuffixHom = 0) (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    differential A (s.spanOnePrefixRhs a ha) =
      ((n : ℤ) + 1).negOnePow •
        compose A s.spanSuffixRhs (s.edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) (by omega) := by
  rw [s.spanOnePrefixRhs_differential hknown a ha, spanSuffixResidual_eq, hzero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left]
  simp only [differential, map_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_sub, smul_neg, neg_neg]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanOnePrefixRhs_differential_of_suffix_zero)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
