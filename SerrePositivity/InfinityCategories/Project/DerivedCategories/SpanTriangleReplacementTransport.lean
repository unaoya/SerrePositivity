module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanTriangleSuffixReplacement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanTriangleFirstReplacement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanSuffixReplacementTransport

/-! # 二成分挿入後の三角形右辺の型付き比較

概要：Q と A の二つの置換による最上位右辺を、共通の型付き Hom の線形式へ移す。
方針：後続置換の合成項と A 置換の削除項を順に移し、変化の式を足す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の最上位未知方程式の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- Q と A を挿入した三角形右辺は、二つの既知の変化の和に異種等号で一致する。 -/
lemma spanInsertUnknowns_triangle_rhs_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D (n + 3))
    (q : GradedHom R (s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)) (s.obj (Fin.last (n + 3))) (-(n : ℤ)))
    (a : GradedHom R (s.obj 0) (s.obj (Fin.last (n + 3))) (-(n : ℤ) - 1))
    (hzeroQ : s.spanSuffixHom = 0)
    (hzeroA : ∀ x y k hI hx hy hk,
      s.hom (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk = 0)
    {X P Y : D} (hx : s.obj 0 = X) (hp : s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) = P)
    (hy : s.obj (Fin.last (n + 3)) = Y)
    {l : ℤ} (hl : -(n : ℤ) - 2 + 1 = l)
    (q' : GradedHom R P Y (l + 1)) (a' r : GradedHom R X Y l)
    (t : GradedHom R X P (-1))
    (hq : HEq q q') (ha : HEq a a') (hr : HEq s.spanTwoPrefixRhs r)
    (ht : HEq (s.tripleHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) t) :
    HEq (s.spanInsertUnknowns q a).spanTwoPrefixRhs
      (r - ((n : ℤ) + 1).negOnePow • compose R q' t (by omega) +
        ((n : ℤ) + 2).negOnePow • a') := by
  let sq := s.replaceFixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega) q
  have Hq := s.spanTwoPrefixRhs_replace_suffix
    (s.fixedHomFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (Fin.last (n + 3)) (-(n : ℤ))
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces_max n _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]; push_cast; omega) q)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_self, hzeroQ, sub_zero] at Hq
  have hqdeg : -(n : ℤ) = l + 1 := by omega
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) hx hp hy rfl hqdeg hl
    _ _ q' t hq ht (by omega) (by omega)
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.gradedHom_units_smul_heq (R := R) hx hy hl ((n : ℤ) + 1).negOnePow _ _ hc
  have hsub := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_sub_heq (A := R) hx hy hl _ _ _ _ hr hs
  have hqval : sq.spanTwoPrefixRhs = s.spanTwoPrefixRhs -
      ((n : ℤ) + 1).negOnePow •
        compose R q (s.tripleHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) (by omega) := by
    exact (sub_eq_iff_eq_add.mp Hq).trans (by abel)
  have hsq := (heq_of_eq hqval).trans hsub
  have Ha := sq.spanTwoPrefixRhs_replace_first
    (sq.fixedHomFamily (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3)) (-(n : ℤ) - 1)
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
      (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; push_cast; omega) a)
  have hne : insert (0 : Fin (n + 4)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
    intro h
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanFirst_insert_not_subset n
    rw [h]
  have hz : ∀ x y k hI hx hy hk,
      sq.hom (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
    intro x y k hI hx hy hk
    unfold sq _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_of_ne (hne := hne)]
    exact hzeroA x y k hI hx hy hk
  rw [hz, sub_zero] at Ha
  have hfa := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq sq (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n))
    0 (Fin.last (n + 3)) (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; push_cast; omega) a
    0 (Fin.last (n + 3)) (-(n : ℤ) - 2 + 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; push_cast; omega)
  have hsa := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.gradedHom_units_smul_heq (R := R) hx hy hl ((n : ℤ) + 2).negOnePow
    _ _ (hfa.trans ha)
  have hadd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (A := R) hx hy hl _ _ _ _ hsq hsa
  have hval := (sub_eq_iff_eq_add.mp Ha).trans (add_comm _ _)
  exact (heq_of_eq hval).trans hadd

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (spanInsertUnknowns_triangle_rhs_heq)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
