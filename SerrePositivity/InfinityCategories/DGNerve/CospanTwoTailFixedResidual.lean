module
public import SerrePositivity.InfinityCategories.DGNerve.CospanTwoTailCoordinates
public import SerrePositivity.InfinityCategories.DGNerve.CospanResidualCoordinates

/-! # 固定次数の三角形側残差の微分

概要：三角形側の Bianchi を全て固定した次数の右辺で表示する。
方針：濃度による次数を −n の式へそろえ、証明の一意性を使う。
規約：HA Proposition 1.3.1.10。使われ方：型付き三角形残差の整合式を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：三角形側の計算で使う D 側右辺を、全体右辺の微分と同じ次数で評価する。
方針：末尾一点追加集合の右辺の次数を −n−2+1 に指定する。
規約：HA Proposition 1.3.1.10。使われ方：合成の和を同じ斉次 Hom で取る。 -/
def cospanTwoTailLastRhs {n : ℕ} (s : SimplexData A D (n + 3)) :
    GradedHom A (s.obj 0) (s.obj (cospanLastTail n)) (-(n : ℤ) - 2 + 1 + 1) :=
  s.rhs (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
    (-(n : ℤ) - 2 + 1)
    (by rw [card_cospanPrefix_insert _
          ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
    (cospanPrefix_insert_min _ _)
    (cospanPrefix_insert_max _
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
    (by rw [card_cospanPrefix_insert _
          ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
        push_cast
        omega)

/-- 概要：零未知データの固定次数の三角形側右辺の微分は三つの右辺の合成の和。
方針：生の Bianchi に固定次数を代入し、濃度と端点の同定で各右辺をそろえる。
規約：HA Proposition 1.3.1.10。使われ方：δr_BD=r_D−g r_B−u r₀ の型付き移送。 -/
lemma cospanTwoTailRhs_differential_of_unknown_zero {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I)
    (hzero : ∀ I, cospanPrefixFaces n ⊆ I →
      ∀ a b k hI ha hb hk, s.hom I a b k hI ha hb hk = 0) :
    differential A s.cospanTwoTailRhs =
      -(compose A (n := -(n : ℤ) - 2 + 1 + 1)
          (s.tripleHom (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
          (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
          s.cospanPrefixRhs (by omega) +
        (-s.cospanTwoTailLastRhs +
          compose A (n := -(n : ℤ) - 2 + 1 + 1) (s.edgeHom (cospanFirstTail n) (cospanLastTail n)
            (cospanFirstTail_lt_lastTail n))
            (s.cospanOneTailRhs (cospanFirstTail n) (cospanApex_lt_firstTail n))
            (by omega))) := by
  dsimp only [cospanTwoTailRhs]
  rw [s.differential_rhs_cospan_twoTail_of_unknown_zero hknown hzero]
  dsimp only [cospanPrefixRhs, cospanOneTailRhs, cospanTwoTailLastRhs]
  congr 1
  all_goals congr 1
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [card_cospanPrefixFaces, Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [card_cospanPrefixFaces,
    card_cospanPrefix_insert _ (cospanApex_lt_firstTail n),
    Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | (simp only [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n),
        Nat.cast_add, Nat.cast_ofNat]; omega)

/-- 概要：同じ集合・端点の右辺は、有効な次数をどう指定しても異種等号で一致する。
方針：二つの次数は濃度から等しいので消去し、証明の一意性を使う。
規約：HA Construction 1.3.1.6。使われ方：三角形側の D 右辺を脚側の D 右辺と同定する。 -/
lemma rhs_heq_of_degrees {m : ℕ} (s : SimplexData A D m)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k l : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hl : l = 2 - (I.card : ℤ)) :
    HEq (s.rhs I a b k hI ha hb hk) (s.rhs I a b l hI ha hb hl) := by
  have hkl : k = l := hk.trans hl.symm
  cases hkl
  rfl

/-- 概要：三角形側計算の D 右辺と脚側計算の D 右辺は異種等号で一致する。
方針：同じ右辺の有効な次数指定の独立性を使う。
規約：HA Proposition 1.3.1.10。使われ方：左右で共通に選んだ r_D へ移送する。 -/
lemma cospanTwoTailLastRhs_heq {n : ℕ} (s : SimplexData A D (n + 3)) :
    HEq s.cospanTwoTailLastRhs (s.cospanOneTailRhs (cospanLastTail n)
      ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))) := by
  unfold cospanTwoTailLastRhs cospanOneTailRhs
  exact s.rhs_heq_of_degrees _ _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
