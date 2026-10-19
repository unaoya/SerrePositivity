module
public import SerrePositivity.InfinityCategories.Derived.DGRoofSliceVertices
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.DGNerve.PinchedPiZero

/-! # pinched Hom の閉頂点と標的 slice の一致

概要：閉零射からの pinched 頂点は、標準 slice 表示で同じ閉射の実 over 頂点になる。
方針：零単体の pinched 同値が元の辺を保つことを使う。
規約：全端点を固定する。使われ方：実屋根の fiber と指定屋根頂点の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉零射に対応する実 pinched Hom の頂点。 -/
def pinchedClosedVertex {q y : D}
    (f : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) y) :
    (DGNerve.pinchedHom A D q y) _⦋0⦌ :=
  (DGNerve.PinchedHom.vertexClosedEquiv q y).symm f

/-- 閉零射の pinched 頂点の元の一単体は、その閉射の実辺。 -/
lemma pinchedClosedVertex_val {q y : D}
    (f : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) y) :
    (pinchedClosedVertex A D f).val = (dgClosedEdge A D f).edge := rfl

/-- 閉零射の pinched 頂点の slice 表示は、同じ閉射の実 over 頂点。 -/
lemma pinchedClosedVertex_slice {q y : D}
    (f : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) y) :
    ((pinchedHomSliceFiberIso (X := dgNerve A D)
      (Simplex.vertex q) (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
        (Simplex.vertex q)).app (Opposite.op ⦋0⦌) (pinchedClosedVertex A D f) =
      dgClosedOverVertex A D f := rfl

/-- 始域の等式による輸送は、元の標的 slice への包含を変えない。 -/
lemma dgPinchedSourceTransport_slice (q q' y : D) (h : q = q') :
    (eqToIso (congrArg (fun z => DGNerve.pinchedHom A D z y) h)).inv ≫
      (pinchedHomSliceFiberIso (X := dgNerve A D)
        (Simplex.vertex q) (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
        (Simplex.vertex q) =
      (pinchedHomSliceFiberIso (X := dgNerve A D)
        (Simplex.vertex q') (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
        (Simplex.vertex q') := by
  subst q'
  simp

end SerrePositivity.InfinityCategories
