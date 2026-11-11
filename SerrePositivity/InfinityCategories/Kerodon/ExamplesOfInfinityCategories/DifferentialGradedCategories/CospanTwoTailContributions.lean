module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanTwoTailBianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom

/-! # 三角形成分の Bianchi の個々の寄与

概要：標準セル全体の二つの残差寄与を、脚とホモトピーの成分の合成として評価する。
方針：錐頂点と最初の末尾頂点で削除・切断を同定し、既知残差と符号を整理する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の三角形の残差整合条件。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：全体集合の錐頂点の残差寄与は、三角形成分と先頭残差の合成。
方針：削除集合と右切断の残差を消し、正一の HA 符号と次数 −1 の微分合成則の符号を使う。
規約：HA Proposition 1.3.1.10。使われ方：三角形の残差式の u r₀ に対応する項。 -/
lemma cospan_twoTail_contribution_apex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    s.residualContribution Finset.univ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) k hI ha hb hk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (Finset.mem_univ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) =
      compose A (s.tripleHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
        (s.residual (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)
          (2 - ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).card : ℤ))
          (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; omega)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_max n _) rfl)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega) := by
  let V : Finset (Fin (n + 4)) := Finset.univ
  have hdel := hknown (V.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_erase_known V (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le _).mpr le_rfl))
  have hright := hknown (V.filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n ≤ ·))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_rightCut_known V (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n))
  dsimp only [V] at hdel hright
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.residualContribution]
  rw [s.residual_zero_of_equation _ hdel, s.residual_zero_of_equation _ hright]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero, zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_sign_apex, one_smul,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_leftCut_apex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_rightCut_apex]
  have hAB := ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
  have hBD := ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)
  have hAD := ne_of_lt ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
  have hcard : ({_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n} :
      Finset (Fin (n + 4))).card = 3 := by simp [hAB, hBD, hAD]
  have hc : ((Finset.univ : Finset (Fin (n + 4))).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n ≤ ·)).card = 3 := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_rightCut_apex, hcard]
  simp only [hcard, Nat.cast_ofNat]
  norm_num only [Int.negOnePow_neg, Int.negOnePow_one]
  simp only [Units.neg_smul, one_smul, neg_neg]
  congr 1
  all_goals try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_leftCut_apex, hc, Nat.cast_ofNat]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_leftCut_apex, hc, Nat.cast_ofNat]
  all_goals omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospan_twoTail_contribution_apex)


/-- 概要：最初の末尾頂点の残差寄与は、D 側残差の負と cospan の射との合成の和。
方針：右切断の既知残差を消し、削除集合と左切断を二つの末尾一点追加集合へ同定する。
規約：HA Proposition 1.3.1.10。使われ方：三角形の残差式の r_D と g r_B に対応する項。 -/
lemma cospan_twoTail_contribution_firstTail {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    s.residualContribution Finset.univ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) k hI ha hb hk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (Finset.mem_univ _)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n) =
      -(s.residual (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
        (k + 1)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _
              ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))]; omega)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_min _ _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_max _
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) _)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _
              ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega)) +
      compose A (s.edgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))
        (s.residual (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n)
          (2 - ((insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).card : ℤ))
          (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)]; omega)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_min _ _)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_max _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) _) rfl)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega) := by
  have hpos := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
  have hright := hknown ((Finset.univ : Finset (Fin (n + 4))).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n ≤ ·))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_rightCut_known Finset.univ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) hpos)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.residualContribution]
  rw [s.residual_zero_of_equation _ hright]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_sign_firstTail, Units.neg_smul, one_smul,
    neg_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_leftCut_firstTail, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_rightCut_firstTail,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_erase_firstTail]
  have hpair : ({_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n} : Finset (Fin (n + 4))).card = 2 := by
    simp [ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)]
  have hc : ((Finset.univ : Finset (Fin (n + 4))).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n ≤ ·)).card = 2 := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_rightCut_firstTail, hpair]
  simp only [hpair, Nat.cast_ofNat, sub_self, Int.negOnePow_zero, one_smul]
  rw [sub_eq_add_neg]
  conv_lhs => rw [add_comm]
  congr 1
  all_goals try dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
  all_goals congr 1
  all_goals try simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_leftCut_firstTail, hc, Nat.cast_ofNat, sub_self]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | rfl
    | exact proof_irrel_heq _ _
    | simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanUniv_leftCut_firstTail, hc, Nat.cast_ofNat, sub_self]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospan_twoTail_contribution_firstTail)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
