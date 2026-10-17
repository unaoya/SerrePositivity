module
public import SerrePositivity.InfinityCategories.DGNerve.CospanTwoTailContributions

/-! # 三角形成分の右辺の微分

概要：三角形側の右辺の微分を先頭と二つの脚側の残差により表示する。
方針：Bianchi の二寄与の抽出と個々の寄与の計算を合成する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の未知六成分の残差整合条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：三角形側の右辺の微分は三角形成分と先頭残差の合成、D 側残差の負、脚側残差との合成の和。
方針：全体集合の Bianchi を二項に制限し、それぞれを削除と切断の公式で計算する。
規約：HA Proposition 1.3.1.10。使われ方：零未知データで δr_BD=r_D−g r_B−u r₀ を得る。 -/
lemma differential_rhs_cospan_twoTail {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : cospanLastTail n = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    differential A (s.rhs Finset.univ 0 (cospanLastTail n) k hI ha hb hk) =
      compose A (s.tripleHom (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
        (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
        (s.residual (cospanPrefixFaces n) 0 (cospanApex n)
          (2 - ((cospanPrefixFaces n).card : ℤ))
          (by rw [card_cospanPrefixFaces]; omega)
          (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _) rfl)
        (by rw [card_cospanPrefixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega) +
      (-(s.residual (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
        (k + 1)
        (by rw [card_cospanPrefix_insert _
              ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
        (cospanPrefix_insert_min _ _)
        (cospanPrefix_insert_max _
          ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
        (by rw [card_cospanPrefix_insert _
              ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega)) +
      compose A (s.edgeHom (cospanFirstTail n) (cospanLastTail n)
        (cospanFirstTail_lt_lastTail n))
        (s.residual (insert (cospanFirstTail n) (cospanPrefixFaces n)) 0 (cospanFirstTail n)
          (2 - ((insert (cospanFirstTail n) (cospanPrefixFaces n)).card : ℤ))
          (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; omega)
          (cospanPrefix_insert_min _ _)
          (cospanPrefix_insert_max _ (cospanApex_lt_firstTail n) _) rfl)
        (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega)) := by
  rw [s.differential_rhs_cospan_twoTail_pair hknown k hI ha hb hk,
    s.cospan_twoTail_contribution_apex hknown k hI ha hb hk,
    s.cospan_twoTail_contribution_firstTail hknown k hI ha hb hk]

/-- 概要：零未知データでは三角形側右辺の微分は先頭と脚側右辺の三項の線形結合。
方針：未知集合の残差を各右辺の負へ書き換え、合成の線形性で負号を外へ出す。
規約：HA Proposition 1.3.1.10。使われ方：δr_BD=r_D−g r_B−u r₀ と同値の式。 -/
lemma differential_rhs_cospan_twoTail_of_unknown_zero {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I)
    (hzero : ∀ I, cospanPrefixFaces n ⊆ I →
      ∀ a b k hI ha hb hk, s.hom I a b k hI ha hb hk = 0) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : cospanLastTail n = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    differential A (s.rhs Finset.univ 0 (cospanLastTail n) k hI ha hb hk) =
      -(compose A (s.tripleHom (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
        (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
        (s.rhs (cospanPrefixFaces n) 0 (cospanApex n)
          (2 - ((cospanPrefixFaces n).card : ℤ))
          (by rw [card_cospanPrefixFaces]; omega)
          (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _) rfl)
        (by rw [card_cospanPrefixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega) +
      (-(s.rhs (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
        (k + 1)
        (by rw [card_cospanPrefix_insert _
              ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]; omega)
        (cospanPrefix_insert_min _ _)
        (cospanPrefix_insert_max _
          ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) _)
        (by rw [card_cospanPrefix_insert _
              ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega)) +
      compose A (s.edgeHom (cospanFirstTail n) (cospanLastTail n)
        (cospanFirstTail_lt_lastTail n))
        (s.rhs (insert (cospanFirstTail n) (cospanPrefixFaces n)) 0 (cospanFirstTail n)
          (2 - ((insert (cospanFirstTail n) (cospanPrefixFaces n)).card : ℤ))
          (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; omega)
          (cospanPrefix_insert_min _ _)
          (cospanPrefix_insert_max _ (cospanApex_lt_firstTail n) _) rfl)
        (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega))) := by
  rw [s.differential_rhs_cospan_twoTail hknown k hI ha hb hk]
  dsimp only [residual]
  simp only [hzero (cospanPrefixFaces n) Finset.Subset.rfl,
    hzero (insert (cospanFirstTail n) (cospanPrefixFaces n)) (Finset.subset_insert _ _),
    hzero (insert (cospanLastTail n) (cospanPrefixFaces n)) (Finset.subset_insert _ _),
    differential, map_zero]
  rw [compose_sub_right, compose_sub_right]
  simp only [compose_zero, zero_sub, neg_add, neg_neg]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
