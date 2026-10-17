module
public import SerrePositivity.InfinityCategories.DGNerve.CospanResidualCoordinates

/-! # 末尾一点の右辺の微分と先頭残差の合成

概要：脚側の方程式の右辺の微分は、その脚と先頭の残差の合成になる。
方針：Bianchi の唯一の錐頂点の寄与を展開し、削除と右切断の既知残差を消去する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の脚側の残差整合条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：末尾一点を加えた右辺の微分は脚と先頭の残差の合成。
方針：錐頂点の Bianchi の寄与を二点の右切断と先頭の左切断で評価し、二つの負号を相殺する。
規約：HA Proposition 1.3.1.10。使われ方：未知成分を零としたとき δr_B=−p r₀ を得る。 -/
lemma differential_rhs_cospan_oneTail {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I)
    (b : Fin (n + 4)) (hb : cospanApex n < b) (k : ℤ)
    (hI : 2 ≤ (insert b (cospanPrefixFaces n)).card)
    (ha : (0 : Fin (n + 4)) = (insert b (cospanPrefixFaces n)).min' (Index.nonempty hI))
    (hmax : b = (insert b (cospanPrefixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert b (cospanPrefixFaces n)).card : ℤ)) :
    differential A (s.rhs (insert b (cospanPrefixFaces n)) 0 b k hI ha hmax hk) =
      compose A (s.edgeHom (cospanApex n) b hb)
        (s.residual (cospanPrefixFaces n) 0 (cospanApex n)
          (2 - ((cospanPrefixFaces n).card : ℤ))
          (by rw [card_cospanPrefixFaces]; omega)
          (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _) rfl)
        (by rw [card_cospanPrefix_insert b hb] at hk
            rw [card_cospanPrefixFaces]
            push_cast at hk ⊢
            omega) := by
  rw [s.differential_rhs_cospan_oneTail_single hknown b hb]
  let I := insert b (cospanPrefixFaces n)
  have hdel := hknown (I.erase (cospanApex n))
    (cospan_erase_known I (cospanApex n) ((mem_cospanPrefixFaces_iff_le _).mpr le_rfl))
  have hright := hknown (I.filter (cospanApex n ≤ ·))
    (cospan_rightCut_known I (cospanApex n) (cospanApex_pos n))
  dsimp only [I] at hdel hright
  dsimp only [residualContribution]
  rw [s.residual_zero_of_equation _ hdel, s.residual_zero_of_equation _ hright]
  simp only [zero_compose, sub_zero, zero_sub]
  simp only [cospanPrefix_insert_leftCut, cospanPrefix_insert_rightCut b hb,
    Finset.card_pair (ne_of_lt hb), Nat.cast_ofNat, sub_self,
    Int.negOnePow_zero, one_smul, cospanPrefix_insert_sign b hb]
  simp only [Units.neg_smul, one_smul, neg_neg]
  congr 1
  all_goals try simp only [edgeHom, cospanPrefix_insert_leftCut, cospanPrefix_insert_rightCut b hb,
    Finset.card_pair (ne_of_lt hb), Nat.cast_ofNat, sub_self]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | simp only [cospanPrefix_insert_leftCut, cospanPrefix_insert_rightCut b hb,
        Finset.card_pair (ne_of_lt hb), Nat.cast_ofNat, sub_self]

/-- 概要：固定次数の脚側の右辺の微分は、脚と固定次数の先頭残差の合成。
方針：脚側の Bianchi に固定した次数を代入し、先頭の濃度の式で次数を同定する。
規約：HA Proposition 1.3.1.10。使われ方：複体の Hom 座標へ渡す残差整合条件。 -/
lemma cospanOneTailRhs_differential {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I)
    (b : Fin (n + 4)) (hb : cospanApex n < b) :
    differential A (s.cospanOneTailRhs b hb) =
      compose A (s.edgeHom (cospanApex n) b hb) s.cospanPrefixResidual (by omega) := by
  dsimp only [cospanOneTailRhs]
  rw [s.differential_rhs_cospan_oneTail hknown b hb]
  dsimp only [cospanPrefixResidual]
  congr 1
  all_goals try exact proof_irrel_heq _ _
  all_goals try (simp only [card_cospanPrefixFaces, Nat.cast_add, Nat.cast_ofNat]; omega)
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | (simp only [card_cospanPrefixFaces, Nat.cast_add, Nat.cast_ofNat]; omega)

/-- 概要：先頭の未知成分を零としたデータでは、脚側右辺の微分は脚と先頭右辺の合成の負。
方針：先頭残差を右辺の負に書き換え、合成の差に対する線形性を使う。
規約：HA Proposition 1.3.1.10。使われ方：N7.1 の δr_B=−p r₀ 等の整合条件。 -/
lemma cospanOneTailRhs_differential_of_prefix_zero {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I)
    (hzero : s.cospanPrefixHom = 0) (b : Fin (n + 4)) (hb : cospanApex n < b) :
    differential A (s.cospanOneTailRhs b hb) =
      -compose A (s.edgeHom (cospanApex n) b hb) s.cospanPrefixRhs (by omega) := by
  rw [s.cospanOneTailRhs_differential hknown b hb, cospanPrefixResidual_eq, hzero,
    compose_sub_right]
  simp only [differential, map_zero, compose_zero, zero_sub]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
