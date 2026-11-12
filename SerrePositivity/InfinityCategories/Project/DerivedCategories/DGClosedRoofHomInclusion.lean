module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofHomInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexSlice

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉分母の実頂点から回収した始域は、元の閉分母の始域。 -/
lemma dgClosedRoofSource_eq (P : Set D) (x : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s).val =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left := by
  exact congrArg (fun z => z.obj 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex_source A D P x s)

/-- 指定閉分母上に、その元の始域からの Hom 全体を含める。 -/
def dgClosedRoofHomInclusion (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y :=
  (eqToIso (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y)
    (dgClosedRoofSource_eq A D P x s))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofHomInclusion A D P x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s)

/-- 閉分母上の Hom 包含は、元の指定閉分母に定値。 -/
lemma dgClosedRoofHomInclusion_projection (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    dgClosedRoofHomInclusion A D P x y s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s) := by
  rw [dgClosedRoofHomInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofHomInclusion_projection, SSet.comp_const]

/-- 閉分母上の Hom 包含の標的 slice は、元の始域の pinched Hom の標準表示。 -/
lemma dgClosedRoofHomInclusion_target (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    dgClosedRoofHomInclusion A D P x y s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) s.obj.left)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) s.obj.left)) := by
  rw [dgClosedRoofHomInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofHomInclusion_target]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedSourceTransport_slice A D _ _ y (dgClosedRoofSource_eq A D P x s)

/-- 閉分母上の閉分子の pinched 頂点は、指定厳密屋根頂点そのもの。 -/
lemma dgClosedRoofHomInclusion_closedVertex (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (f : s.obj.left ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (dgClosedRoofHomInclusion A D P x y s).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofVertex A D P x y s f := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackSimplex_ext
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f))
      (dgClosedRoofHomInclusion_target A D P x y s)
    exact h.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex_slice A D f).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofVertex_target A D P x y s f).symm)
  · have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f))
      (dgClosedRoofHomInclusion_projection A D P x y s)
    exact h.trans (by
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero _).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictRoofVertex_projection A D P x y s f).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
