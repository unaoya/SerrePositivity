module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofSpans
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPointSliceEdgePostcomposition

/-! # 任意標的の実屋根の指定頂点の二射影

概要：元の実屋根の像と、標的の固定 Hom 頂点の屋根内の像の二成分を厳密に計算する。
方針：全空間写像の射影公式を零単体で評価し、実辺の slice 表示と照合する。
規約：頂点を選び直さない。使われ方：評価三角形の実屋根内の辺の両端を固定する。
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

/-- 元の実 span 屋根の任意標的像の第一成分は、指定分子の実像の slice 頂点。 -/
lemma dgInvertingRoofFunctorMap_span_target (P : Set D) (x y : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofSpan A D P x y) :
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      (SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex A D P x y r)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex (r.numerator.map ((truncation 2).map F)) := by
  have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex A D P x y r)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_target A D P x y F)
  change _ = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex A D P x y r)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex_target, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_postcomp] at h
  exact h

/-- 元の実 span 屋根の任意標的像の第二成分は、指定実分母の頂点。 -/
lemma dgInvertingRoofFunctorMap_span_projection (P : Set D) (x y : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofSpan A D P x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))).app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex A D P x y r)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanDenominatorVertex A D P x y r := by
  have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex A D P x y r)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_projection A D P x y F)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex_projection A D P x y r)

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 標的の指定実辺の固定 Hom 包含の第一成分は、その実辺の slice 頂点。 -/
lemma dgInvertingFixedHomRoofMap_edge_target (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) {z : Y _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj Y)
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) z) :
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F z).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm e)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex e := by
  have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm e)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_target A D P x F z)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPinchedVertex_slice e)

/-- 標的の指定実辺の固定 Hom 包含の第二成分は、元の恒等分母の頂点。 -/
lemma dgInvertingFixedHomRoofMap_edge_projection (P : Set D) (x : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) {z : Y _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj Y)
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F z).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F z).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm e)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x := by
  have h := congrArg (fun G => G.app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm e)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_projection A D P x F z)
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x) 0 at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
