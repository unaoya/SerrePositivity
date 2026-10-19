module
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixContributions

/-! # 二固定頂点の方程式の残差による微分

概要：全体方程式の右辺の微分を、後続と二つの脚側の残差により表示する。
方針：Bianchi の二寄与の抽出と各寄与の展開を合成し、零未知データでは線形性で右辺へ移す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の六成分の残差整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：全体方程式の右辺の微分は二つの符号付き残差項の和。
方針：二寄与の Bianchi に個々の寄与の式を代入する。
規約：次数は全体集合の濃度で指定する。使われ方：零未知データの三項の整合条件。 -/
lemma differential_rhs_span_twoPrefix {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ spanSuffixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : Fin.last (n + 3) = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    differential A (s.rhs Finset.univ 0 (Fin.last (n + 3)) k hI ha hb hk) =
      ((n : ℤ) + 1).negOnePow •
        (-compose A (s.residual (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3))
          (2 - ((spanSuffixFaces n).card : ℤ))
          (by rw [card_spanSuffixFaces]; omega)
          (spanSuffixFaces_min n _) (spanSuffixFaces_max n _) rfl)
        (s.tripleHom 0 (spanSecondPrefix n) (spanApex n)
          (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n))
        (by rw [card_spanSuffixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega)) +
      ((n : ℤ) + 2).negOnePow •
        (s.residual (insert (0 : Fin (n + 4)) (spanSuffixFaces n)) 0 (Fin.last (n + 3))
          (k + 1)
          (by rw [card_spanSuffix_insert _ (spanApex_pos n)]; omega)
          (spanSuffix_insert_min _ (spanApex_pos n) _) (spanSuffix_insert_max _ _)
          (by rw [card_spanSuffix_insert _ (spanApex_pos n)]
              simp only [Finset.card_univ, Fintype.card_fin] at hk
              push_cast at hk ⊢
              omega) -
        compose A (s.residual (insert (spanSecondPrefix n) (spanSuffixFaces n))
          (spanSecondPrefix n) (Fin.last (n + 3))
          (2 - ((insert (spanSecondPrefix n) (spanSuffixFaces n)).card : ℤ))
          (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; omega)
          (spanSuffix_insert_min _ (spanSecondPrefix_lt_apex n) _) (spanSuffix_insert_max _ _) rfl)
          (s.edgeHom 0 (spanSecondPrefix n) (spanSecondPrefix_pos n))
          (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]
              simp only [Finset.card_univ, Fintype.card_fin] at hk
              push_cast at hk ⊢
              omega)) := by
  rw [s.differential_rhs_span_twoPrefix_pair hknown k hI ha hb hk,
    s.span_twoPrefix_contribution_apex hknown k hI ha hb hk,
    s.span_twoPrefix_contribution_secondPrefix hknown k hI ha hb hk]

/-- 概要：零未知データでは全体右辺の微分を三つの右辺の符号付きの線形結合にする。
方針：未知集合の残差を右辺の負に変え、合成とスカラー倍の線形性を使う。
規約：一般の閉性や解の存在を仮定しない。使われ方：cofiber の有限残差系への入力。 -/
lemma differential_rhs_span_twoPrefix_of_unknown_zero {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ spanSuffixFaces n ⊆ I → s.Equation I)
    (hzero : ∀ I, spanSuffixFaces n ⊆ I →
      ∀ a b k hI ha hb hk, s.hom I a b k hI ha hb hk = 0) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : Fin.last (n + 3) = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    differential A (s.rhs Finset.univ 0 (Fin.last (n + 3)) k hI ha hb hk) =
      -(((n : ℤ) + 1).negOnePow •
        (-compose A (s.rhs (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3))
          (2 - ((spanSuffixFaces n).card : ℤ))
          (by rw [card_spanSuffixFaces]; omega)
          (spanSuffixFaces_min n _) (spanSuffixFaces_max n _) rfl)
        (s.tripleHom 0 (spanSecondPrefix n) (spanApex n)
          (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n))
        (by rw [card_spanSuffixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega)) +
      ((n : ℤ) + 2).negOnePow •
        (s.rhs (insert (0 : Fin (n + 4)) (spanSuffixFaces n)) 0 (Fin.last (n + 3))
          (k + 1)
          (by rw [card_spanSuffix_insert _ (spanApex_pos n)]; omega)
          (spanSuffix_insert_min _ (spanApex_pos n) _) (spanSuffix_insert_max _ _)
          (by rw [card_spanSuffix_insert _ (spanApex_pos n)]
              simp only [Finset.card_univ, Fintype.card_fin] at hk
              push_cast at hk ⊢
              omega) -
        compose A (s.rhs (insert (spanSecondPrefix n) (spanSuffixFaces n))
          (spanSecondPrefix n) (Fin.last (n + 3))
          (2 - ((insert (spanSecondPrefix n) (spanSuffixFaces n)).card : ℤ))
          (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; omega)
          (spanSuffix_insert_min _ (spanSecondPrefix_lt_apex n) _) (spanSuffix_insert_max _ _) rfl)
          (s.edgeHom 0 (spanSecondPrefix n) (spanSecondPrefix_pos n))
          (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]
              simp only [Finset.card_univ, Fintype.card_fin] at hk
              push_cast at hk ⊢
              omega))) := by
  rw [s.differential_rhs_span_twoPrefix hknown k hI ha hb hk]
  dsimp only [residual]
  simp only [hzero (spanSuffixFaces n) Finset.Subset.rfl,
    hzero (insert (0 : Fin (n + 4)) (spanSuffixFaces n)) (Finset.subset_insert _ _),
    hzero (insert (spanSecondPrefix n) (spanSuffixFaces n)) (Finset.subset_insert _ _),
    differential, map_zero]
  rw [compose_sub_left, compose_sub_left]
  simp only [zero_compose, sub_eq_add_neg, smul_add, smul_neg, neg_add, neg_neg,
    zero_add]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
