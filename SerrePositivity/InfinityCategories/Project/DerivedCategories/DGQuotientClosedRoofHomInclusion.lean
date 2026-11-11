module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedRoofHomInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexSlice

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 指定閉分母上に、その元の始域からの Hom 全体を含める。 -/
def dgQuotientClosedRoofHomInclusion (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y :=
  (eqToIso (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
    ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofSource_eq A D P x s))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofHomInclusion A D P x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s)

/-- 閉分母上の Hom 包含は、元の指定閉分母に定値。 -/
lemma dgQuotientClosedRoofHomInclusion_projection (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    dgQuotientClosedRoofHomInclusion A D P x y s ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s) := by
  rw [dgQuotientClosedRoofHomInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofHomInclusion_projection,
    SSet.comp_const]

/-- 閉分母上の Hom 包含の標的 slice は、元の始域の pinched Hom の標準表示。 -/
lemma dgQuotientClosedRoofHomInclusion_target (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    dgQuotientClosedRoofHomInclusion A D P x y s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceTarget A D P x y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))) := by
  rw [dgQuotientClosedRoofHomInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofHomInclusion_target]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedSourceTransport_slice A (DGQuotient.QuotientObject D P) _ _
    ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
    (congrArg (DGQuotient.inclusion A D P).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofSource_eq A D P x s))

/-- 閉分母上の閉分子の pinched 頂点は、指定厳密屋根頂点そのもの。 -/
lemma dgQuotientClosedRoofHomInclusion_closedVertex (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.obj s.obj.left ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) :
    (dgQuotientClosedRoofHomInclusion A D P x y s).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (DGQuotient.QuotientObject D P) f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictQuotientRoofVertex A D P x y s f := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackSimplex_ext
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (DGQuotient.QuotientObject D P) f))
      (dgQuotientClosedRoofHomInclusion_target A D P x y s)
    exact h.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex_slice A (DGQuotient.QuotientObject D P) f).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictQuotientRoofVertex_target A D P x y s f).symm)
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (DGQuotient.QuotientObject D P) f))
      (dgQuotientClosedRoofHomInclusion_projection A D P x y s)
    exact h.trans (by
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero _).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictQuotientRoofVertex_projection A D P x y s f).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
