module
public import SerrePositivity.InfinityCategories.Derived.DGSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdgeCompositionEquality

/-! # 元の実単体と閉細分辺の厳密一致による始点細分の一致

概要：元の単体と追加閉射の実辺が等しければ、任意次数の細分単体全体も厳密に等しい。
方針：単体・始対象の等式を消去し、実閉辺の単射性を使う。
規約：全 cochain を含む厳密等式。使われ方：高次指定面の共有面の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の単体と閉細分辺が一致すれば、任意次数の実細分単体全体も一致する。 -/
lemma dgSimplexInitialRefinement_congr {n : ℕ} {t t' : Simplex A D n} (ht : t = t')
    (q q' : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (s' : ForgetEnrichment.of (Complex A) q' ⟶ ForgetEnrichment.of (Complex A) (t'.obj 0))
    (hs : (dgClosedEdge A D s).edge = (dgClosedEdge A D s').edge) :
    dgSimplexInitialRefinement A D t q s = dgSimplexInitialRefinement A D t' q' s' := by
  cases ht
  have hq : q = q' := congrArg (fun a : Simplex A D 1 => a.obj 0) hs
  cases hq
  cases dgClosedEdge_raw_injective A D s s' hs
  rfl

end SerrePositivity.InfinityCategories
