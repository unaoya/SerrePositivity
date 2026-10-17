module
public import SerrePositivity.InfinityCategories.DGNerve.CospanTwoTailBianchi
public import SerrePositivity.InfinityCategories.DGNerve.TripleHom

/-! # 三角形成分の Bianchi の個々の寄与

概要：標準セル全体の二つの残差寄与を、脚とホモトピーの成分の合成として評価する。
方針：錐頂点と最初の末尾頂点で削除・切断を同定し、既知残差と符号を整理する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の三角形の残差整合条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：全体集合の錐頂点の残差寄与は、三角形成分と先頭残差の合成。
方針：削除集合と右切断の残差を消し、正一の HA 符号と次数 −1 の微分合成則の符号を使う。
規約：HA Proposition 1.3.1.10。使われ方：三角形の残差式の u r₀ に対応する項。 -/
lemma cospan_twoTail_contribution_apex {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : cospanLastTail n = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    s.residualContribution Finset.univ 0 (cospanLastTail n) k hI ha hb hk
        (cospanApex n) (Finset.mem_univ _) (cospanApex_pos n)
        ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n)) =
      compose A (s.tripleHom (cospanApex n) (cospanFirstTail n) (cospanLastTail n)
        (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
        (s.residual (cospanPrefixFaces n) 0 (cospanApex n)
          (2 - ((cospanPrefixFaces n).card : ℤ))
          (by rw [card_cospanPrefixFaces]; omega)
          (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _) rfl)
        (by rw [card_cospanPrefixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega) := by
  let V : Finset (Fin (n + 4)) := Finset.univ
  have hdel := hknown (V.erase (cospanApex n))
    (cospan_erase_known V (cospanApex n) ((mem_cospanPrefixFaces_iff_le _).mpr le_rfl))
  have hright := hknown (V.filter (cospanApex n ≤ ·))
    (cospan_rightCut_known V (cospanApex n) (cospanApex_pos n))
  dsimp only [V] at hdel hright
  dsimp only [residualContribution]
  rw [s.residual_zero_of_equation _ hdel, s.residual_zero_of_equation _ hright]
  simp only [zero_compose, sub_zero, zero_sub, cospanUniv_sign_apex, one_smul,
    cospanUniv_leftCut_apex, cospanUniv_rightCut_apex]
  have hAB := ne_of_lt (cospanApex_lt_firstTail n)
  have hBD := ne_of_lt (cospanFirstTail_lt_lastTail n)
  have hAD := ne_of_lt ((cospanApex_lt_firstTail n).trans (cospanFirstTail_lt_lastTail n))
  have hcard : ({cospanApex n, cospanFirstTail n, cospanLastTail n} :
      Finset (Fin (n + 4))).card = 3 := by simp [hAB, hBD, hAD]
  have hc : ((Finset.univ : Finset (Fin (n + 4))).filter (cospanApex n ≤ ·)).card = 3 := by
    rw [cospanUniv_rightCut_apex, hcard]
  simp only [hcard, Nat.cast_ofNat]
  norm_num only [Int.negOnePow_neg, Int.negOnePow_one]
  simp only [Units.neg_smul, one_smul, neg_neg]
  congr 1
  all_goals try simp only [tripleHom, cospanUniv_leftCut_apex, hc, Nat.cast_ofNat]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | simp only [cospanUniv_leftCut_apex, hc, Nat.cast_ofNat]
  all_goals omega

/-- 概要：最初の末尾頂点の残差寄与は、D 側残差の負と cospan の射との合成の和。
方針：右切断の既知残差を消し、削除集合と左切断を二つの末尾一点追加集合へ同定する。
規約：HA Proposition 1.3.1.10。使われ方：三角形の残差式の r_D と g r_B に対応する項。 -/
lemma cospan_twoTail_contribution_firstTail {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ cospanPrefixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : cospanLastTail n = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    s.residualContribution Finset.univ 0 (cospanLastTail n) k hI ha hb hk
        (cospanFirstTail n) (Finset.mem_univ _)
        ((cospanApex_pos n).trans (cospanApex_lt_firstTail n)) (cospanFirstTail_lt_lastTail n) =
      -(s.residual (insert (cospanLastTail n) (cospanPrefixFaces n)) 0 (cospanLastTail n)
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
            omega) := by
  have hpos := (cospanApex_pos n).trans (cospanApex_lt_firstTail n)
  have hright := hknown ((Finset.univ : Finset (Fin (n + 4))).filter (cospanFirstTail n ≤ ·))
    (cospan_rightCut_known Finset.univ (cospanFirstTail n) hpos)
  dsimp only [residualContribution]
  rw [s.residual_zero_of_equation _ hright]
  simp only [zero_compose, sub_zero, cospanUniv_sign_firstTail, Units.neg_smul, one_smul,
    neg_sub, cospanUniv_leftCut_firstTail, cospanUniv_rightCut_firstTail,
    cospanUniv_erase_firstTail]
  have hpair : ({cospanFirstTail n, cospanLastTail n} : Finset (Fin (n + 4))).card = 2 := by
    simp [ne_of_lt (cospanFirstTail_lt_lastTail n)]
  have hc : ((Finset.univ : Finset (Fin (n + 4))).filter (cospanFirstTail n ≤ ·)).card = 2 := by
    rw [cospanUniv_rightCut_firstTail, hpair]
  simp only [hpair, Nat.cast_ofNat, sub_self, Int.negOnePow_zero, one_smul]
  rw [sub_eq_add_neg]
  conv_lhs => rw [add_comm]
  congr 1
  all_goals try dsimp only [edgeHom]
  all_goals congr 1
  all_goals try simp only [cospanUniv_leftCut_firstTail, hc, Nat.cast_ofNat, sub_self]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | rfl
    | exact proof_irrel_heq _ _
    | simp only [cospanUniv_leftCut_firstTail, hc, Nat.cast_ofNat, sub_self]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
