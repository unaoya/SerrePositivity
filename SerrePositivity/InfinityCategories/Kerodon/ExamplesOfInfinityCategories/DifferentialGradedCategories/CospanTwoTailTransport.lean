module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanTwoTailFixedResidual

/-! # 三角形側整合式の型付き Hom への移送

概要：三角形側 Bianchi を指定した対象・次数の斉次射の式へ移す。
方針：微分・合成・和・負の異種等号を組み合わせる。
規約：HA Proposition 1.3.1.10。使われ方：標準 fiber の実際の残差整合式。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：三角形側 Bianchi は異種等号で指定された Hom 座標でも成り立つ。
方針：生の右辺の三項をそれぞれ移してから同じ Hom の等号へ戻す。
規約：HA Proposition 1.3.1.10。使われ方：r_BD,r_CD の微分を同じ r₀,r_D で表示する。 -/
lemma cospan_twoTail_differential_of_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I → s.Equation I)
    (hzero : ∀ I, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I →
      ∀ a b k hI ha hb hk, s.hom I a b k hI ha hb hk = 0)
    {X P B Y : D} (hx : s.obj 0 = X) (hP : s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = P)
    (hB : s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) = B) (hy : s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) = Y)
    {l : ℤ} (hl : -(n : ℤ) - 2 + 1 = l)
    (r0 : GradedHom A X P (l + 1 + 1))
    (rB : GradedHom A X B (l + 1)) (rD : GradedHom A X Y (l + 1))
    (rT : GradedHom A X Y l) (g : GradedHom A B Y 0) (u : GradedHom A P Y (-1))
    (h0 : HEq s.cospanPrefixRhs r0)
    (hfirst : HEq (s.cospanOneTailRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)) rB)
    (hlast : HEq s.cospanTwoTailLastRhs rD)
    (hT : HEq s.cospanTwoTailRhs rT)
    (hg : HEq (s.edgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) g)
    (hu : HEq (s.tripleHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) u) :
    differential A rT =
      -(compose A (n := l + 1) u r0 (by omega) +
        (-rD + compose A g rB (add_zero (l + 1)))) := by
  have hl1 : -(n : ℤ) - 2 + 1 + 1 = l + 1 := by omega
  have hl0 : -(n : ℤ) + 1 = l + 1 + 1 := by omega
  have hlB : -(n : ℤ) - 1 + 1 = l + 1 := by omega
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy hl _ _ hT
  have hc0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hP hy hl0 rfl hl1
    _ _ u r0 hu h0 (by omega) (by omega)
  have hcB := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hB hy hlB rfl hl1
    _ _ g rB hg hfirst (by omega) (add_zero (l + 1))
  have hnD := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_neg_heq (A := A) hx hy hl1 _ _ hlast
  have hsB := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (A := A) hx hy hl1 _ _ _ _ hnD hcB
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (A := A) hx hy hl1 _ _ _ _ hc0 hsB
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_neg_heq (A := A) hx hy hl1 _ _ hs
  exact eq_of_heq (hd.symm.trans
    ((heq_of_eq (s.cospanTwoTailRhs_differential_of_unknown_zero hknown hzero)).trans hn))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospan_twoTail_differential_of_heq)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
