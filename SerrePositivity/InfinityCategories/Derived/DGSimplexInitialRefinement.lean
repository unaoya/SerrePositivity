module
public import SerrePositivity.InfinityCategories.Derived.DGSimplexDataInitialRefinement

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {n : ℕ} (t : Simplex A D n) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))

/-- 全ての実方程式を保つ、任意次数の同じ閉始点細分。 -/
def dgSimplexInitialRefinement : Simplex A D n where
  toSimplexData := dgSimplexDataInitialRefinement A D t.toSimplexData q s
  equation I a b k hI ha hb hk := by
    change differential A
      (dgSourceRefinementHomLinear A D t.obj q s a b k (t.hom I a b k hI ha hb hk)) = _
    exact (dgSourceRefinementHomLinear_differential A D t.obj q s a b k _).trans
      ((congrArg (dgSourceRefinementHomLinear A D t.obj q s a b (k + 1))
        (t.equation I a b k hI ha hb hk)).trans
          (dgSimplexDataInitialRefinement_rhs A D t.toSimplexData q s I a b k hI ha hb hk))

/-- 細分した実単体の始対象は指定 q。 -/
lemma dgSimplexInitialRefinement_obj_zero : (dgSimplexInitialRefinement A D t q s).obj 0 = q :=
  dgSourceRefinementObj_zero D t.obj q

/-- 細分した実単体の正番号の対象は元のまま。 -/
lemma dgSimplexInitialRefinement_obj_ne_zero (i : Fin (n + 1)) (hi : i ≠ 0) :
    (dgSimplexInitialRefinement A D t q s).obj i = t.obj i :=
  dgSourceRefinementObj_ne_zero D t.obj q i hi

end SerrePositivity.InfinityCategories
