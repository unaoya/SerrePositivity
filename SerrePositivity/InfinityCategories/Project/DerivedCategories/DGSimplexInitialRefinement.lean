module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplexDataInitialRefinement

/-! # 任意次数の実 dg 単体の閉始点細分

概要：元の単体の始点だけを同じ閉射で細分し、全ての dg 単体方程式を保つ。
方針：微分の可換性、元の方程式、rhs の輸送を接続する。
規約：全次数、零次を含む。使われ方：四次以降の最後外ホーンの指定面の同時細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {n : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0))

/-- 全ての実方程式を保つ、任意次数の同じ閉始点細分。 -/
def dgSimplexInitialRefinement : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t.toSimplexData q s
  equation I a b k hI ha hb hk := by
    change _root_.SerrePositivity.DifferentialGraded.differential A
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D t.obj q s a b k (t.hom I a b k hI ha hb hk)) = _
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_differential A D t.obj q s a b k _).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D t.obj q s a b (k + 1))
        (t.equation I a b k hI ha hb hk)).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_rhs A D t.toSimplexData q s I a b k hI ha hb hk))

/-- 細分した実単体の始対象は指定 q。 -/
lemma dgSimplexInitialRefinement_obj_zero : (dgSimplexInitialRefinement A D t q s).obj 0 = q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_zero D t.obj q

/-- 細分した実単体の正番号の対象は元のまま。 -/
lemma dgSimplexInitialRefinement_obj_ne_zero (i : Fin (n + 1)) (hi : i ≠ 0) :
    (dgSimplexInitialRefinement A D t q s).obj i = t.obj i :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementObj_ne_zero D t.obj q i hi

end SerrePositivity.InfinityCategories.Project.DerivedCategories
