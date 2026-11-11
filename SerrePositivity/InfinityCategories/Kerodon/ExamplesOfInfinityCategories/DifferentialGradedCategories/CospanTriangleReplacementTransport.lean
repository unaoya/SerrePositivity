module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanTriangleDReplacement
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanPrefixReplacementTransport

/-! # 二成分置換後の三角形右辺の型付き検証

概要：先頭と D 側の成分を挿入した三角形右辺は、型付きの線形式が零なら零になる。
方針：二つの置換の変化を異種等号で同じ Hom へ移して足す。
規約：HA Proposition 1.3.1.10。使われ方：候補データの最後の未知方程式の検証。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：二成分を挿入した三角形右辺は r−u a−d=0 という型付きの式から零になる。
方針：先頭置換の変化 −u a と D 置換の変化 −d を足し、同じ Hom の式へ移す。
規約：HA Proposition 1.3.1.10。使われ方：候補の全体集合の右辺を消す。 -/
lemma cospanTwoTailRhs_replace_zero_of_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (fA : ∀ a b k (hM : 2 ≤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).card),
      a = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      b = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      k = 2 - ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (fD : ∀ a b k (hM : 2 ≤ (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).card),
      a = (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      b = (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      k = 2 - ((insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).card : ℤ) →
      GradedHom A (s.obj a) (s.obj b) k)
    (hzero : s.cospanPrefixHom = 0)
    (hDzero : (s.replace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) fA).cospanTriangleD_Hom = 0)
    {X P Y : D} (hx : s.obj 0 = X) (hP : s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = P)
    (hy : s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) = Y) {l : ℤ} (hl : -(n : ℤ) - 2 + 1 = l)
    (a : GradedHom A X P (l + 1)) (d r : GradedHom A X Y l) (u : GradedHom A P Y (-1))
    (ha : HEq (s.cospanPrefixReplacementHom fA) a)
    (hd : HEq (((s.replace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) fA).replace
      (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) fD).cospanTriangleD_Hom) d)
    (hr : HEq s.cospanTwoTailRhs r)
    (hu : HEq (s.tripleHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) u)
    (hsolve : r - compose A u a (by omega) - d = 0) :
    ((s.replace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) fA).replace
      (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) fD).cospanTwoTailRhs = 0 := by
  let t := s.replace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) fA
  let w := t.replace (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) fD
  have HA := s.cospanTwoTailRhs_replace_prefix fA
  change t.cospanTwoTailRhs - s.cospanTwoTailRhs =
    -compose A _ (s.cospanPrefixReplacementHom fA - s.cospanPrefixHom) _ at HA
  rw [hzero, sub_zero] at HA
  have hdeg : -(n : ℤ) = l + 1 := by omega
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hP hy hdeg rfl hl _ _ u a hu ha
    (by omega) (by omega)
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_neg_heq (A := A) hx hy hl _ _ hc
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (A := A) hx hy hl _ _ _ _ hr hn
  have hAval := (sub_eq_iff_eq_add.mp HA).trans (add_comm _ _)
  have hAtyped : HEq t.cospanTwoTailRhs (r - compose A u a (by omega)) := by
    simpa only [sub_eq_add_neg] using (heq_of_eq hAval).trans hs
  have HD := t.cospanTwoTailRhs_replace_D fD
  have hDval := t.replace_hom_same (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) fD
    0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (-(n : ℤ) - 2 + 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_min _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_max _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))]
        push_cast
        omega)
  change w.cospanTriangleD_Hom = _ at hDval
  rw [← hDval] at HD
  rw [hDzero, sub_zero] at HD
  have hnD := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_neg_heq (A := A) hx hy hl _ _ hd
  have htotal := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (A := A) hx hy hl _ _ _ _ hnD hAtyped
  have hsolve' : -d + (r - compose A u a (by omega)) = 0 := by
    calc
      _ = r - compose A u a (by omega) - d := by abel
      _ = 0 := hsolve
  have ht := (heq_of_eq (sub_eq_iff_eq_add.mp HD)).trans
    (htotal.trans (heq_of_eq hsolve'))
  exact eq_of_heq (ht.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) hx hy hl).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospanTwoTailRhs_replace_zero_of_heq)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
