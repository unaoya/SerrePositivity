module
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofHomInclusion
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedVertexSlice

/-! # 指定元の閉分母上の商 Hom の実商屋根への包含

概要：指定閉分母の元の始域の Hom を、同じ実分母上の実屋根に含める。
方針：回収した始域と元の始域の等式で輸送し、実 fiber の包含と合成する。
規約：元の始域を選び直さない。使われ方：閉細分による有限比較の実全空間化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定閉分母上に、その元の始域からの Hom 全体を含める。 -/
def dgQuotientClosedRoofHomInclusion (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((DGQuotient.inclusion A D P).obj y) ⟶
      dgQuotientRoofCorrespondence A D P x y :=
  (eqToIso (congrArg (fun q => DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
    ((DGQuotient.inclusion A D P).obj q) ((DGQuotient.inclusion A D P).obj y))
    (dgClosedRoofSource_eq A D P x s))).inv ≫
      dgQuotientRoofHomInclusion A D P x y (dgClosedVerdierDenominatorVertex A D P x s)

/-- 閉分母上の Hom 包含は、元の指定閉分母に定値。 -/
lemma dgQuotientClosedRoofHomInclusion_projection (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    dgQuotientClosedRoofHomInclusion A D P x y s ≫
      dgQuotientRoofCorrespondenceProjection A D P x y =
      SSet.const (dgClosedVerdierDenominatorVertex A D P x s) := by
  rw [dgQuotientClosedRoofHomInclusion, Category.assoc, dgQuotientRoofHomInclusion_projection,
    SSet.comp_const]

/-- 閉分母上の Hom 包含の標的 slice は、元の始域の pinched Hom の標準表示。 -/
lemma dgQuotientClosedRoofHomInclusion_target (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    dgQuotientClosedRoofHomInclusion A D P x y s ≫ dgQuotientRoofCorrespondenceTarget A D P x y =
      (pinchedHomSliceFiberIso (X := dgQuotientNerve A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj
          (ForgetEnrichment.to (Complex A) s.obj.left)))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
          (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj
          (ForgetEnrichment.to (Complex A) s.obj.left))) := by
  rw [dgQuotientClosedRoofHomInclusion, Category.assoc, dgQuotientRoofHomInclusion_target]
  exact dgPinchedSourceTransport_slice A (DGQuotient.QuotientObject D P) _ _
    ((DGQuotient.inclusion A D P).obj y)
    (congrArg (DGQuotient.inclusion A D P).obj (dgClosedRoofSource_eq A D P x s))

/-- 閉分母上の閉分子の pinched 頂点は、指定厳密屋根頂点そのもの。 -/
lemma dgQuotientClosedRoofHomInclusion_closedVertex (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x)
    (f : (DGQuotient.inclusion A D P).onClosed.obj s.obj.left ⟶
      ForgetEnrichment.of (Complex A) ((DGQuotient.inclusion A D P).obj y)) :
    (dgQuotientClosedRoofHomInclusion A D P x y s).app (Opposite.op ⦋0⦌)
      (pinchedClosedVertex A (DGQuotient.QuotientObject D P) f) =
      dgStrictQuotientRoofVertex A D P x y s f := by
  apply roofPullbackSimplex_ext
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (pinchedClosedVertex A (DGQuotient.QuotientObject D P) f))
      (dgQuotientClosedRoofHomInclusion_target A D P x y s)
    exact h.trans ((pinchedClosedVertex_slice A (DGQuotient.QuotientObject D P) f).trans
      (dgStrictQuotientRoofVertex_target A D P x y s f).symm)
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (pinchedClosedVertex A (DGQuotient.QuotientObject D P) f))
      (dgQuotientClosedRoofHomInclusion_projection A D P x y s)
    exact h.trans (by
      exact (PinchedHom.constant_zero _).trans
        (dgStrictQuotientRoofVertex_projection A D P x y s f).symm)

end SerrePositivity.InfinityCategories
