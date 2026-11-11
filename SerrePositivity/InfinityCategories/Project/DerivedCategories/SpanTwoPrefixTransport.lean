module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanOnePrefixTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanTwoPrefixCoordinates

/-! # 三角形側の符号付き微分条件の Hom への移送

概要：三角形側 Bianchi を指定された対象と次数の三項の式へ移す。
方針：微分・合成・和・差・符号スカラーの異種等号を合成する。
規約：可換環上の任意の dg 圏。使われ方：D7 の cochain 座標での残差整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：零未知データの三角形側微分公式は指定された Hom 座標でも成り立つ。
方針：三項を個別に移し、共通の符号倍の異種等号と微分の比較を合成する。
規約：共通係数は (-1)^(n+1)。使われ方：六成分線形系の二つの三角形条件。 -/
lemma span_twoPrefix_differential_of_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (hzero : ∀ I, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I →
      ∀ a b k hI ha hb hk, s.hom I a b k hI ha hb hk = 0)
    {X P B Y : D} (hx : s.obj 0 = X) (hP : s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) = P)
    (hB : s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) = B) (hy : s.obj (Fin.last (n + 3)) = Y)
    {l : ℤ} (hl : -(n : ℤ) - 2 + 1 = l)
    (r0 : GradedHom A P Y (l + 1 + 1)) (rB : GradedHom A B Y (l + 1))
    (rA : GradedHom A X Y (l + 1)) (rT : GradedHom A X Y l)
    (g : GradedHom A X B 0) (u : GradedHom A X P (-1))
    (h0 : HEq s.spanSuffixRhs r0)
    (hfirst : HEq (s.spanOnePrefixRhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) rB)
    (hA : HEq s.spanTwoPrefixFirstRhs rA) (hT : HEq s.spanTwoPrefixRhs rT)
    (hg : HEq (s.edgeHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)) g)
    (hu : HEq (s.tripleHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) u) :
    differential A rT = ((n : ℤ) + 1).negOnePow •
      (compose A (n := l + 1) r0 u (by omega) + rA -
        compose A rB g (zero_add (l + 1))) := by
  have hl1 : -(n : ℤ) - 2 + 1 + 1 = l + 1 := by omega
  have hl0 : -(n : ℤ) + 1 = l + 1 + 1 := by omega
  have hlB : -(n : ℤ) - 1 + 1 = l + 1 := by omega
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy hl _ _ hT
  have hc0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hP hy rfl hl0 hl1
    _ _ r0 u h0 hu (by omega) (by omega)
  have hcB := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hB hy rfl hlB hl1
    _ _ rB g hfirst hg (by omega) (zero_add (l + 1))
  have hs0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (A := A) hx hy hl1 _ _ _ _ hc0 hA
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_sub_heq (A := A) hx hy hl1 _ _ _ _ hs0 hcB
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_gradedHom_units_smul_heq (A := A) hx hy hl1
    ((n : ℤ) + 1).negOnePow _ _ hs
  exact eq_of_heq (hd.symm.trans
    ((heq_of_eq
      (s.spanTwoPrefixRhs_differential_of_unknown_zero_normalized hknown hzero)).trans hc))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (span_twoPrefix_differential_of_heq)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
