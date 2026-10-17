module
public import SerrePositivity.InfinityCategories.DGNerve.CospanTwoTailResidual
public import SerrePositivity.InfinityCategories.DGNerve.CospanBoundaryUnknownZero

/-! # 実際の境界の三角形成分の残差整合条件

概要：左右の零未知境界データの三角形側右辺の微分を、先頭と脚側の右辺で表示する。
方針：実際の既知方程式と全未知成分の零を三角形版 Bianchi に渡す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の fiber の座標に渡す最後の残差条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左の零未知境界データでは三角形側の右辺の微分が先頭と脚側の右辺の三項に分かれる。
方針：全ての既知方程式と未知成分の零を実際の境界から証明して三角形の残差公式を適用する。
規約：HA Proposition 1.3.1.10。使われ方：標準 fiber の Hom 座標へ渡す三角形側の整合性。 -/
lemma cospanBoundaryLeftZeroData_twoTail_differential {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : cospanLastTail n = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    differential A ((cospanBoundaryLeftZeroData F).rhs Finset.univ 0 (cospanLastTail n) k hI ha
      hb hk) =
      -(compose A ((cospanBoundaryLeftZeroData F).tripleHom (cospanApex n) (cospanFirstTail n)
        (cospanLastTail n)
        (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
        ((cospanBoundaryLeftZeroData F).rhs (cospanPrefixFaces n) 0 (cospanApex n)
          (2 - ((cospanPrefixFaces n).card : ℤ))
          (by rw [card_cospanPrefixFaces]; omega)
          (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _) rfl)
        (by rw [card_cospanPrefixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega) +
      (-((cospanBoundaryLeftZeroData F).rhs (insert (cospanLastTail n) (cospanPrefixFaces n)) 0
        (cospanLastTail n)
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
      compose A ((cospanBoundaryLeftZeroData F).edgeHom (cospanFirstTail n) (cospanLastTail n)
        (cospanFirstTail_lt_lastTail n))
        ((cospanBoundaryLeftZeroData F).rhs (insert (cospanFirstTail n) (cospanPrefixFaces n)) 0
          (cospanFirstTail n)
          (2 - ((insert (cospanFirstTail n) (cospanPrefixFaces n)).card : ℤ))
          (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; omega)
          (cospanPrefix_insert_min _ _)
          (cospanPrefix_insert_max _ (cospanApex_lt_firstTail n) _) rfl)
        (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega))) :=
  (cospanBoundaryLeftZeroData F).differential_rhs_cospan_twoTail_of_unknown_zero
    (cospanBoundaryLeftData_equation F _) (cospanBoundaryLeftZeroData_unknownHom F)
    k hI ha hb hk

/-- 概要：右の零未知境界データでは三角形側の右辺の微分が先頭と脚側の右辺の三項に分かれる。
方針：全ての既知方程式と未知成分の零を実際の境界から証明して三角形の残差公式を適用する。
規約：HA Proposition 1.3.1.10。使われ方：標準 fiber の Hom 座標へ渡す三角形側の整合性。 -/
lemma cospanBoundaryRightZeroData_twoTail_differential {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D)
    (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : cospanLastTail n = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    differential A ((cospanBoundaryRightZeroData F).rhs Finset.univ 0 (cospanLastTail n) k hI ha
      hb hk) =
      -(compose A ((cospanBoundaryRightZeroData F).tripleHom (cospanApex n) (cospanFirstTail n)
        (cospanLastTail n)
        (cospanApex_lt_firstTail n) (cospanFirstTail_lt_lastTail n))
        ((cospanBoundaryRightZeroData F).rhs (cospanPrefixFaces n) 0 (cospanApex n)
          (2 - ((cospanPrefixFaces n).card : ℤ))
          (by rw [card_cospanPrefixFaces]; omega)
          (cospanPrefixFaces_min n _) (cospanPrefixFaces_max n _) rfl)
        (by rw [card_cospanPrefixFaces]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega) +
      (-((cospanBoundaryRightZeroData F).rhs (insert (cospanLastTail n) (cospanPrefixFaces n)) 0
        (cospanLastTail n)
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
      compose A ((cospanBoundaryRightZeroData F).edgeHom (cospanFirstTail n) (cospanLastTail n)
        (cospanFirstTail_lt_lastTail n))
        ((cospanBoundaryRightZeroData F).rhs (insert (cospanFirstTail n) (cospanPrefixFaces n)) 0
          (cospanFirstTail n)
          (2 - ((insert (cospanFirstTail n) (cospanPrefixFaces n)).card : ℤ))
          (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]; omega)
          (cospanPrefix_insert_min _ _)
          (cospanPrefix_insert_max _ (cospanApex_lt_firstTail n) _) rfl)
        (by rw [card_cospanPrefix_insert _ (cospanApex_lt_firstTail n)]
            simp only [Finset.card_univ, Fintype.card_fin] at hk
            push_cast at hk ⊢
            omega))) :=
  (cospanBoundaryRightZeroData F).differential_rhs_cospan_twoTail_of_unknown_zero
    (cospanBoundaryRightData_equation F _) (cospanBoundaryRightZeroData_unknownHom F)
    k hI ha hb hk

end SerrePositivity.InfinityCategories.DGNerve
