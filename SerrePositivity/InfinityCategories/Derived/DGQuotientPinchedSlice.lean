module
public import SerrePositivity.InfinityCategories.Derived.DGRoofCorrespondenceMap
public import SerrePositivity.InfinityCategories.Core.Roof.RoofPinchedSlicePostcomp
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap

/-! # 商による実 pinched Hom と実 target slice の可換性

概要：商の Hom 鎖写像による pinched 写像は、元の target slice の商写像と一致する。
方針：pinched の後合成と slice の後合成の可換性に、dg 関手の鎖写像の公式を使う。
規約：全次数で厳密に可換。使われ方：実屋根の商比較の全 fiber の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商の全 Hom 鎖写像の pinched 作用は、元の実 slice への包含と厳密に可換。 -/
lemma dgQuotientTargetSliceMap_pinched (P : Set D) (q y : D) :
    (pinchedHomSliceFiberIso (X := dgNerve A D) (Simplex.vertex q) (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y))) (Simplex.vertex q) ≫
      dgQuotientTargetSliceMap A D P y =
    pinchedHomChainMap ((DGQuotient.inclusion A D P).map q y) ≫
      (pinchedHomSliceFiberIso (X := dgQuotientNerve A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj q))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
          (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj q)) := by
  rw [← dgFunctor_pinchedHomMap_eq]
  have h := roofPinchedSlice_postcomp (dgQuotientNerveProjection A D P)
    (Simplex.vertex q) (Simplex.vertex y)
    (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) q)
    (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y) (dgQuotientNervePoint A D P y)
  simpa only [dgQuotientTargetSliceMap, dgQuotientNerveProjection, Category.assoc] using h

end SerrePositivity.InfinityCategories
