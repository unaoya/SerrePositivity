module
public import SerrePositivity.InfinityCategories.Derived.DGRoofHomInclusion
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedVertexSlice

/-! # 指定閉分母上の pinched Hom の実屋根への包含

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
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉分母の実頂点から回収した始域は、元の閉分母の始域。 -/
lemma dgClosedRoofSource_eq (P : Set D) (x : D)
    (s : DGClosedVerdierDenominators A D P x) :
    dgOverVertexSource A D x (dgClosedVerdierDenominatorVertex A D P x s).val =
      ForgetEnrichment.to (Complex A) s.obj.left := by
  exact congrArg (fun z => z.obj 0) (dgClosedVerdierDenominatorVertex_source A D P x s)

/-- 指定閉分母上に、その元の始域からの Hom 全体を含める。 -/
def dgClosedRoofHomInclusion (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y ⟶
      dgRoofCorrespondence A D P x y :=
  (eqToIso (congrArg (fun q => DGNerve.pinchedHom A D q y)
    (dgClosedRoofSource_eq A D P x s))).inv ≫
      dgRoofHomInclusion A D P x y (dgClosedVerdierDenominatorVertex A D P x s)

/-- 閉分母上の Hom 包含は、元の指定閉分母に定値。 -/
lemma dgClosedRoofHomInclusion_projection (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    dgClosedRoofHomInclusion A D P x y s ≫ dgRoofCorrespondenceProjection A D P x y =
      SSet.const (dgClosedVerdierDenominatorVertex A D P x s) := by
  rw [dgClosedRoofHomInclusion, Category.assoc, dgRoofHomInclusion_projection, SSet.comp_const]

/-- 閉分母上の Hom 包含の標的 slice は、元の始域の pinched Hom の標準表示。 -/
lemma dgClosedRoofHomInclusion_target (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    dgClosedRoofHomInclusion A D P x y s ≫ dgRoofCorrespondenceTarget A D P x y =
      (pinchedHomSliceFiberIso (X := dgNerve A D)
        (Simplex.vertex (ForgetEnrichment.to (Complex A) s.obj.left)) (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
        (Simplex.vertex (ForgetEnrichment.to (Complex A) s.obj.left)) := by
  rw [dgClosedRoofHomInclusion, Category.assoc, dgRoofHomInclusion_target]
  exact dgPinchedSourceTransport_slice A D _ _ y (dgClosedRoofSource_eq A D P x s)

/-- 閉分母上の閉分子の pinched 頂点は、指定厳密屋根頂点そのもの。 -/
lemma dgClosedRoofHomInclusion_closedVertex (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x)
    (f : s.obj.left ⟶ ForgetEnrichment.of (Complex A) y) :
    (dgClosedRoofHomInclusion A D P x y s).app (Opposite.op ⦋0⦌)
      (pinchedClosedVertex A D f) = dgStrictRoofVertex A D P x y s f := by
  apply roofPullbackSimplex_ext
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌) (pinchedClosedVertex A D f))
      (dgClosedRoofHomInclusion_target A D P x y s)
    exact h.trans ((pinchedClosedVertex_slice A D f).trans
      (dgStrictRoofVertex_target A D P x y s f).symm)
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌) (pinchedClosedVertex A D f))
      (dgClosedRoofHomInclusion_projection A D P x y s)
    exact h.trans (by
      exact (PinchedHom.constant_zero _).trans
        (dgStrictRoofVertex_projection A D P x y s f).symm)

end SerrePositivity.InfinityCategories
