module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanResidualCoordinates

/-! # 脚側の符号付き微分条件の Hom への移送

概要：生の脚側 Bianchi を指定した対象と次数の斉次 Hom の等式へ移す。
方針：微分・合成・符号スカラーの異種等号を保存し、最後に通常の等号へ戻す。
規約：可換環上の任意の dg 圏。使われ方：D7 の cochain 座標での脚側の整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：端点と次数の等式を伴う異種等号は符号スカラー倍を保つ。
方針：等式を消去して同じ Hom の等号へ戻す。
規約：スカラーは整数の単位。使われ方：Bianchi の負一冪の移送。 -/
lemma span_gradedHom_units_smul_heq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l)
    (c : ℤˣ) (f : GradedHom A x y k) (g : GradedHom A x' y' l) (h : HEq f g) :
    HEq (c • f) (c • g) := by
  cases hx
  cases hy
  cases hk
  cases eq_of_heq h
  rfl

namespace SimplexData

/-- 概要：零後続成分を持つデータの脚側微分条件を指定された Hom へ移す。
方針：生の微分条件の微分・合成・符号倍を異種等号で移す。
規約：係数は (-1)^(n+1)。使われ方：標準 cofiber の六成分系の脚側条件。 -/
lemma span_onePrefix_differential_of_heq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (hzero : s.spanSuffixHom = 0) (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
    {X P Y : D} (hx : s.obj a = X) (hP : s.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) = P)
    (hy : s.obj (Fin.last (n + 3)) = Y) {l : ℤ} (hl : -(n : ℤ) - 1 + 1 = l)
    (r0 : GradedHom A P Y (l + 1)) (rB : GradedHom A X Y l) (g : GradedHom A X P 0)
    (h0 : HEq s.spanSuffixRhs r0) (hB : HEq (s.spanOnePrefixRhs a ha) rB)
    (hg : HEq (s.edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) g) :
    differential A rB = ((n : ℤ) + 1).negOnePow • compose A r0 g (zero_add (l + 1)) := by
  have hδ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy hl (s.spanOnePrefixRhs a ha) rB hB
  have hl0 : -(n : ℤ) + 1 = l + 1 := by omega
  have hlδ := congrArg (fun k : ℤ => k + 1) hl
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hP hy rfl hl0 hlδ
    s.spanSuffixRhs (s.edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) r0 g h0 hg (by omega) (zero_add (l + 1))
  have hs := span_gradedHom_units_smul_heq (A := A) hx hy hlδ
    ((n : ℤ) + 1).negOnePow _ _ hc
  exact eq_of_heq (hδ.symm.trans
    ((heq_of_eq (s.spanOnePrefixRhs_differential_of_suffix_zero hknown hzero a ha)).trans hs))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData (span_onePrefix_differential_of_heq)


end SimplexData
end SerrePositivity.InfinityCategories.Project.DerivedCategories
