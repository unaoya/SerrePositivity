module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofIdentityRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGInvertingRoofVertexProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ActualRoofInvertingEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofPullbackEdge

/-! # 評価三角形による任意標的の実屋根内の比較辺

概要：元の実屋根の像と、その指定評価辺の固定 Hom 包含を実屋根全空間内の辺で比較する。
方針：評価三角形の slice 辺と恒等分母への実細分辺を、始域成分の厳密一致で組にする。
規約：評価辺・評価三角形・実分母の全てを保持する。使われ方：高次 Hom 作用族との比較。
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
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
variable (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofSpan A D P x y) (E : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofEvaluation F r)

/-- 評価三角形を保つ、任意標的の実屋根内の実比較辺。 -/
def dgActualRoofEvaluationTargetEdge :
    Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex A D P x y r))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))).app
        (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm E.value)) := by
  let a := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex A D P x y r)
  let b := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm E.value)
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F
  let u : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))))
      ((pullback.fst p s).app (Opposite.op ⦋0⦌) a)
      ((pullback.fst p s).app (Opposite.op ⦋0⦌) b) := {
    edge := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge E.triangle).edge
    src_eq := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge E.triangle).src_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_span_target A D P x y F r).symm
    tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge E.triangle).tgt_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_edge_target A D P x F E.value).symm }
  let v : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
      ((pullback.snd p s).app (Opposite.op ⦋0⦌) a)
      ((pullback.snd p s).app (Opposite.op ⦋0⦌) b) := {
    edge := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofDenominatorIdentityEdge A D P x y r).edge
    src_eq := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofDenominatorIdentityEdge A D P x y r).src_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_span_projection A D P x y F r).symm
    tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofDenominatorIdentityEdge A D P x y r).tgt_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_edge_projection A D P x F E.value).symm }
  have h : p.app (Opposite.op ⦋1⦌) u.edge = s.app (Opposite.op ⦋1⦌) v.edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge E.triangle).edge =
      F.app (Opposite.op ⦋1⦌) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofDenominatorIdentityEdge A D P x y r).edge)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge_projection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofDenominatorIdentityEdge_source]
    rfl
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackEdge p s u v h

/-- 実屋根内の評価比較辺は、元の実分母から恒等分母への指定細分辺の上にある。 -/
lemma dgActualRoofEvaluationTargetEdge_projection :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))).app
      (Opposite.op ⦋1⦌) (dgActualRoofEvaluationTargetEdge A D P x y F r E).edge =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofDenominatorIdentityEdge A D P x y r).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackEdge_snd _ _ _ _ _

/-- 実屋根内の評価比較辺は、元の評価三角形全体を実射側成分として持つ。 -/
lemma dgActualRoofEvaluationTargetEdge_target :
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F)).app
        (Opposite.op ⦋1⦌) (dgActualRoofEvaluationTargetEdge A D P x y F r E).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge E.triangle).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPullbackEdge_fst _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
