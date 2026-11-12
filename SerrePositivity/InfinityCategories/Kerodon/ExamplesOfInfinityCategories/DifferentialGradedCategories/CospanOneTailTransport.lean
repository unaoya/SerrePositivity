module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanOneTailResidual

/-! # 脚側の残差整合式の型付き Hom への移送

概要：生の脚側 Bianchi の式を、指定した対象と次数の Hom の等式へ移す。
方針：微分・合成・負の異種等号の保存を使い、最後に同じ Hom の通常の等号へ戻す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：実際の r_B,r_C の微分整合式。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：既知方程式と先頭成分の零を満たすデータの脚側整合式は、指定した Hom へ移しても成り立つ。
方針：生の Bianchi の式の微分・合成・負を異種等号で移し、固定された対象の等式として読む。
規約：HA Proposition 1.3.1.10。使われ方：標準 fiber の Hom 座標での δr_B=−p r₀ 等を得る。 -/
lemma cospan_oneTail_differential_of_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I → s.Equation I)
    (hzero : s.cospanPrefixHom = 0) (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b)
    {X P Y : D} (hx : s.obj 0 = X) (hP : s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = P) (hy : s.obj b = Y)
    {l : ℤ} (hl : -(n : ℤ) - 1 + 1 = l)
    (r0 : GradedHom A X P (l + 1)) (rB : GradedHom A X Y l) (g : GradedHom A P Y 0)
    (h0 : HEq s.cospanPrefixRhs r0) (hB : HEq (s.cospanOneTailRhs b hb) rB)
    (hg : HEq (s.edgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) b hb) g) :
    differential A rB = -compose A g r0 (add_zero (l + 1)) := by
  have hδ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy hl
    (s.cospanOneTailRhs b hb) rB hB
  have hl0 : -(n : ℤ) + 1 = l + 1 := by omega
  have hlδ := congrArg (fun k : ℤ => k + 1) hl
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hP hy hl0 rfl hlδ
    (s.edgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) b hb) s.cospanPrefixRhs g r0 hg h0 (by omega) (add_zero (l + 1))
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_neg_heq (A := A) hx hy hlδ _ _ hc
  exact eq_of_heq (hδ.symm.trans
    ((heq_of_eq (s.cospanOneTailRhs_differential_of_prefix_zero hknown hzero b hb)).trans hn))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cospan_oneTail_differential_of_heq)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
