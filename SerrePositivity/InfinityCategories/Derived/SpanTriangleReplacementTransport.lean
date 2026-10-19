module
public import SerrePositivity.InfinityCategories.Derived.SpanTriangleSuffixReplacement
public import SerrePositivity.InfinityCategories.Derived.SpanTriangleFirstReplacement
public import SerrePositivity.InfinityCategories.Derived.SpanSuffixReplacementTransport

/-! # 二成分挿入後の三角形右辺の型付き比較

概要：Q と A の二つの置換による最上位右辺を、共通の型付き Hom の線形式へ移す。
方針：後続置換の合成項と A 置換の削除項を順に移し、変化の式を足す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の最上位未知方程式の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- Q と A を挿入した三角形右辺は、二つの既知の変化の和に異種等号で一致する。 -/
lemma spanInsertUnknowns_triangle_rhs_heq {n : ℕ} (s : SimplexData R D (n + 3))
    (q : GradedHom R (s.obj (spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ)))
    (a : GradedHom R (s.obj 0) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 1))
    (hzeroQ : s.spanSuffixHom = 0)
    (hzeroA : ∀ x y k hI hx hy hk,
      s.hom (insert 0 (spanSuffixFaces n)) x y k hI hx hy hk = 0)
    {X P Y : D} (hx : s.obj 0 = X) (hp : s.obj (spanApex n) = P)
    (hy : s.obj (Fin.last (n + 3)) = Y)
    {l : ℤ} (hl : -(n : ℤ) - 2 + 1 = l)
    (q' : GradedHom R P Y (l + 1)) (a' r : GradedHom R X Y l)
    (t : GradedHom R X P (-1))
    (hq : HEq q q') (ha : HEq a a') (hr : HEq s.spanTwoPrefixRhs r)
    (ht : HEq (s.tripleHom 0 (spanSecondPrefix n) (spanApex n)
      (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n)) t) :
    HEq (s.spanInsertUnknowns q a).spanTwoPrefixRhs
      (r - ((n : ℤ) + 1).negOnePow • compose R q' t (by omega) +
        ((n : ℤ) + 2).negOnePow • a') := by
  let sq := s.replaceFixed (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [card_spanSuffixFaces]; omega)
    (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
    (by rw [card_spanSuffixFaces]; push_cast; omega) q
  have Hq := s.spanTwoPrefixRhs_replace_suffix
    (s.fixedHomFamily (spanSuffixFaces n) (spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
      (by rw [card_spanSuffixFaces]; omega)
      (spanSuffixFaces_min n _) (spanSuffixFaces_max n _)
      (by rw [card_spanSuffixFaces]; push_cast; omega) q)
  rw [fixedHomFamily_self, hzeroQ, sub_zero] at Hq
  have hqdeg : -(n : ℤ) = l + 1 := by omega
  have hc := gradedHom_compose_heq (A := R) hx hp hy rfl hqdeg hl
    _ _ q' t hq ht (by omega) (by omega)
  have hs := gradedHom_units_smul_heq (R := R) hx hy hl ((n : ℤ) + 1).negOnePow _ _ hc
  have hsub := gradedHom_sub_heq (A := R) hx hy hl _ _ _ _ hr hs
  have hqval : sq.spanTwoPrefixRhs = s.spanTwoPrefixRhs -
      ((n : ℤ) + 1).negOnePow •
        compose R q (s.tripleHom 0 (spanSecondPrefix n) (spanApex n)
          (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n)) (by omega) := by
    exact (sub_eq_iff_eq_add.mp Hq).trans (by abel)
  have hsq := (heq_of_eq hqval).trans hsub
  have Ha := sq.spanTwoPrefixRhs_replace_first
    (sq.fixedHomFamily (insert 0 (spanSuffixFaces n)) 0 (Fin.last (n + 3)) (-(n : ℤ) - 1)
      (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
      (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
      (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; push_cast; omega) a)
  have hne : insert (0 : Fin (n + 4)) (spanSuffixFaces n) ≠ spanSuffixFaces n := by
    intro h
    apply spanFirst_insert_not_subset n
    rw [h]
  have hz : ∀ x y k hI hx hy hk,
      sq.hom (insert 0 (spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
    intro x y k hI hx hy hk
    unfold sq replaceFixed
    rw [replace_hom_of_ne (hne := hne)]
    exact hzeroA x y k hI hx hy hk
  rw [hz, sub_zero] at Ha
  have hfa := fixedHomFamily_heq sq (insert 0 (spanSuffixFaces n))
    0 (Fin.last (n + 3)) (-(n : ℤ) - 1)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
    (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; push_cast; omega) a
    0 (Fin.last (n + 3)) (-(n : ℤ) - 2 + 1)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
    (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; push_cast; omega)
  have hsa := gradedHom_units_smul_heq (R := R) hx hy hl ((n : ℤ) + 2).negOnePow
    _ _ (hfa.trans ha)
  have hadd := gradedHom_add_heq (A := R) hx hy hl _ _ _ _ hsq hsa
  have hval := (sub_eq_iff_eq_add.mp Ha).trans (add_comm _ _)
  exact (heq_of_eq hval).trans hadd

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
