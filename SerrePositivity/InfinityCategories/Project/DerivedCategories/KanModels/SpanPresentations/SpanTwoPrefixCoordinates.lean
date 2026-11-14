module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanTwoPrefixResidual
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanResidualCoordinates

/-! # 三角形側の残差の固定次数での微分

概要：全体集合の右辺の微分を固定次数の三つの右辺の合成として表示する。
方針：全体集合の濃度を n+4 として、Bianchi の次数を全て −n の式へそろえる。
規約：HA Proposition 1.3.1.10。使われ方：D7 の cofiber Hom 座標の残差系への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：三角形側の右辺は最初から最後の頂点への次数 −n−2+1 の射。
方針：全体集合の端点と濃度を指定して評価する。
規約：全次元。使われ方：六未知成分の三角形側の右辺。 -/
def spanTwoPrefixRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    GradedHom A (s.obj 0) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 2 + 1) :=
  s.rhs Finset.univ 0 (Fin.last (n + 3)) (-(n : ℤ) - 2)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_min_zero (n + 1) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_max_last (n + 1) _)
    (by simp only [Finset.card_univ, Fintype.card_fin]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanTwoPrefixRhs)


/-- 概要：A 側右辺を三角形側の微分と同じ次数で評価する。
方針：一点追加集合の右辺の次数を −n−2+1 に指定する。
規約：斉次 Hom の次数の式をそろえる。使われ方：右辺の差の型検査。 -/
def spanTwoPrefixFirstRhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    GradedHom A (s.obj 0) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 2 + 1 + 1) :=
  s.rhs (insert (0 : Fin (n + 4)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3))
    (-(n : ℤ) - 2 + 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max _ _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; push_cast; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanTwoPrefixFirstRhs)


/-- 概要：零未知データの三角形側右辺の微分は三つの右辺の符号付き線形結合。
方針：生の二寄与の式に固定次数を代入し、濃度と証明の一意性で型を合わせる。
規約：二つの係数は (-1)^(n+1) と (-1)^(n+2)。使われ方：有限残差系の最後の条件。 -/
lemma spanTwoPrefixRhs_differential_of_unknown_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (hzero : ∀ I, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I →
      ∀ a b k hI ha hb hk, s.hom I a b k hI ha hb hk = 0) :
    differential A s.spanTwoPrefixRhs =
      -(((n : ℤ) + 1).negOnePow •
        (-compose A (n := -(n : ℤ) - 2 + 1 + 1) s.spanSuffixRhs
          (s.tripleHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) (by omega)) +
        ((n : ℤ) + 2).negOnePow •
          (s.spanTwoPrefixFirstRhs -
            compose A (n := -(n : ℤ) - 2 + 1 + 1)
              (s.spanOnePrefixRhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
              (s.edgeHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)) (by omega))) := by
  dsimp only [spanTwoPrefixRhs]
  rw [s.differential_rhs_span_twoPrefix_of_unknown_zero hknown hzero]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixRhs, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs, spanTwoPrefixFirstRhs]
  congr 1
  all_goals congr 1
  all_goals congr 1
  all_goals congr 1
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n), Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | (simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n), Nat.cast_add, Nat.cast_ofNat]; omega)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanTwoPrefixRhs_differential_of_unknown_zero)


/-- 概要：零未知データの三角形側微分は三項の和に共通の符号を掛けた式。
方針：隣り合う負一冪の符号が逆であることと線形性を使う。
規約：共通係数は (-1)^(n+1)。使われ方：六成分線形系の整合条件の簡潔な表示。 -/
lemma spanTwoPrefixRhs_differential_of_unknown_zero_normalized {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (hzero : ∀ I, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I →
      ∀ a b k hI ha hb hk, s.hom I a b k hI ha hb hk = 0) :
    differential A s.spanTwoPrefixRhs =
      ((n : ℤ) + 1).negOnePow •
        (compose A (n := -(n : ℤ) - 2 + 1 + 1) s.spanSuffixRhs
          (s.tripleHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) (by omega) +
          s.spanTwoPrefixFirstRhs -
            compose A (n := -(n : ℤ) - 2 + 1 + 1)
              (s.spanOnePrefixRhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
              (s.edgeHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)) (by omega)) := by
  have hsign : ((n : ℤ) + 2).negOnePow = -((n : ℤ) + 1).negOnePow := by
    have he : (n : ℤ) + 2 = ((n : ℤ) + 1) + 1 := by omega
    rw [he, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]
  rw [s.spanTwoPrefixRhs_differential_of_unknown_zero hknown hzero, hsign]
  simp only [Units.neg_smul, sub_eq_add_neg, smul_add, smul_neg, neg_add, neg_neg]
  abel

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanTwoPrefixRhs_differential_of_unknown_zero_normalized)


/-- 概要：同じ右辺の有効な次数指定を変えても異種等号で一致する。
方針：濃度で決まる二つの次数を同定し、証明の一意性を使う。
規約：全ての集合で使える。使われ方：三角形側と脚側の A 右辺の比較。 -/
lemma rhs_heq_of_span_degrees {m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D m)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k l : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hl : l = 2 - (I.card : ℤ)) :
    HEq (s.rhs I a b k hI ha hb hk) (s.rhs I a b l hI ha hb hl) := by
  have hkl : k = l := hk.trans hl.symm
  cases hkl
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (rhs_heq_of_span_degrees)


/-- 概要：三角形側の A 右辺と脚側の A 右辺は異種等号で一致する。
方針：同じ集合と端点の右辺に次数の指定独立性を使う。
規約：全次元。使われ方：左右で共通の A 側右辺への移送。 -/
lemma spanTwoPrefixFirstRhs_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3)) :
    HEq s.spanTwoPrefixFirstRhs (s.spanOnePrefixRhs 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)) := by
  unfold spanTwoPrefixFirstRhs _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs
  exact s.rhs_heq_of_span_degrees _ _ _ _ _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanTwoPrefixFirstRhs_heq)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
