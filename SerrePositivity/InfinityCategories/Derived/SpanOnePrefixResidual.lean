module
public import SerrePositivity.InfinityCategories.Derived.SpanOnePrefixIndex
public import SerrePositivity.InfinityCategories.Derived.SpanOnePrefixBianchi
public import SerrePositivity.InfinityCategories.DGNerve.Triangle

/-! # 固定一点の右辺の微分と後続残差の合成

概要：脚側の右辺の微分を、後続の共通残差と脚の合成に符号を掛けた式にする。
方針：余錐頂点の単一寄与を展開し、削除と左切断の既知残差を消す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の cofiber Hom 座標の微分整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：固定一点を加えた右辺の微分は後続残差と脚の合成の符号付きの負。
方針：Bianchi の余錐頂点で右切断を後続集合、左切断を二点の脚と同定する。
規約：符号は (-1)^(n+1)。使われ方：脚側の未知方程式の微分条件。 -/
lemma differential_rhs_span_onePrefix {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ spanSuffixFaces n ⊆ I → s.Equation I)
    (a : Fin (n + 4)) (ha : a < spanApex n) (k : ℤ)
    (hI : 2 ≤ (insert a (spanSuffixFaces n)).card)
    (hmin : a = (insert a (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hmax : Fin.last (n + 3) = (insert a (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert a (spanSuffixFaces n)).card : ℤ)) :
    differential A (s.rhs (insert a (spanSuffixFaces n)) a (Fin.last (n + 3)) k hI hmin hmax hk) =
      -(((n : ℤ) + 1).negOnePow •
        compose A (s.residual (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3))
          (2 - ((spanSuffixFaces n).card : ℤ))
          (by rw [card_spanSuffixFaces]; omega)
          (spanSuffixFaces_min n _) (spanSuffixFaces_max n _) rfl)
        (s.edgeHom a (spanApex n) ha)
        (by rw [card_spanSuffix_insert a ha] at hk
            rw [card_spanSuffixFaces]
            push_cast at hk ⊢
            omega)) := by
  rw [s.differential_rhs_span_onePrefix_single hknown a ha]
  let I := insert a (spanSuffixFaces n)
  have hdel := hknown (I.erase (spanApex n))
    (span_erase_known I (spanApex n) ((mem_spanSuffixFaces_iff_le _).mpr le_rfl))
  have hleft := hknown (I.filter (· ≤ spanApex n))
    (span_leftCut_known I (spanApex n) (spanApex_lt_last n))
  dsimp only [I] at hdel hleft
  dsimp only [residualContribution]
  rw [s.residual_zero_of_equation _ hdel, s.residual_zero_of_equation _ hleft]
  simp only [compose_zero, smul_zero, sub_zero, zero_sub]
  simp only [spanSuffix_insert_rightCut a ha, spanSuffix_insert_leftCut a ha,
    spanSuffix_insert_sign a ha, smul_neg]
  congr 2
  simp only [edgeHom]
  congr 1
  all_goals try simp only [spanSuffix_insert_rightCut a ha, spanSuffix_insert_leftCut a ha,
    Finset.card_pair (ne_of_lt ha), Nat.cast_ofNat, sub_self]
  all_goals try exact proof_irrel_heq _ _
  all_goals congr 1
  all_goals first
    | exact proof_irrel_heq _ _
    | simp only [spanSuffix_insert_rightCut a ha, spanSuffix_insert_leftCut a ha,
        Finset.card_pair (ne_of_lt ha), Nat.cast_ofNat, sub_self]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
