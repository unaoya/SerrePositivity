module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual

/-! # 閉始点細分による各既知方程式の保存

概要：全ての方程式を要求せず、入力データの指定集合の方程式だけを同じ細分へ移す。
方針：成分の微分と rhs の同じ線形輸送を接続する。
規約：未知二集合への仮定は不要。使われ方：一般の実ホーンの全体細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {n : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0))

/-- 指定集合の方程式は、同じ閉始点細分で保存される。 -/
lemma dgSimplexDataInitialRefinement_equation (I : Finset (Fin (n + 1))) (hI : t.Equation I) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t q s).Equation I := by
  intro a b k hcard ha hb hk
  change differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D t.obj q s a b k
    (t.hom I a b k hcard ha hb hk)) = _
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_differential A D t.obj q s a b k _).trans
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D t.obj q s a b (k + 1))
      (hI a b k hcard ha hb hk)).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_rhs A D t q s I a b k hcard ha hb hk))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
