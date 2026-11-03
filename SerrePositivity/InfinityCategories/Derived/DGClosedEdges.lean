module
public import SerrePositivity.InfinityCategories.DGNerve.HomotopyCategory
public import SerrePositivity.InfinityCategories.DGNerve.Functor
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 閉 dg 射の実辺とその関手性

概要：元の閉次数零射を指定端点の実辺へ送り、dg 関手による一次単体の像を照合する。
方針：閉零元の実辺表示と、一単体の全データの同値を使う。
規約：対象宇宙が異なる関手でも一次単体の比較は成立。使われ方：native roof の実辺化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉 dg 射を元の対象を端点とする実辺へ送る。 -/
def dgClosedEdge {x y : ClosedCategory A D} (f : x ⟶ y) :
    Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) x))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) y)) :=
  edgeOfCycle (closedHomEquiv A D x y f)

/-- 作った実辺の閉射は元の閉射。 -/
lemma dgClosedEdge_closed {x y : ClosedCategory A D} (f : x ⟶ y) :
    edgeClosed (dgClosedEdge A D f) = f :=
  (closedHomEquiv A D x y).symm_apply_apply f

/-- 元の実辺は、その閉射から作った辺と厳密に一致する。 -/
lemma dgClosedEdge_edgeClosed {x y : ClosedCategory A D}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) x))
      (Simplex.vertex (ForgetEnrichment.to (Complex A) y))) :
    dgClosedEdge A D (edgeClosed e) = e :=
  (edgeClosedEquiv _ _).symm_apply_apply e

/-- dg 関手による閉射の像と実辺の一次単体の像は厳密に一致する。 -/
lemma dgClosedEdge_map {E : Type w} [DGCategory A E] (F : DGFunctor A D E)
    {x y : ClosedCategory A D} (f : x ⟶ y) :
    (dgClosedEdge A D f).edge.map F = (dgClosedEdge A E (F.onClosed.map f)).edge := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    change (F.map x y).f 0 (closedHomEquiv A D x y f).val =
      (closedHomEquiv A E (F.onClosed.obj x) (F.onClosed.obj y) (F.onClosed.map f)).val
    rw [F.closedHomEquiv_map]
    rfl

end SerrePositivity.InfinityCategories
