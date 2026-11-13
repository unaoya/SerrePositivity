module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramFixed
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorEdgeArrowFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
/-!
概要：同じ cospan 上の実錐比較を四角形の区間族へ送る。
方針：slice の全図式表示を転置し、固定境界の各角を定値区間として回収する。
規約：比較辺と全単体を保持する。
使われ方：任意 cofiber と極限錐の比較における三つの固定角。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma sliceSquareDiagramMap_boundaryEvaluation {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) (k : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌) k) =
      SSet.const (p.app (Opposite.op ⦋0⦌) k) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt (X := X) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary k,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_fixed, SSet.const_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]

def sliceSquareIntervalFamily {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p)))

lemma sliceSquareIntervalFamily_boundary {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d)
    (k : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    (sliceSquareIntervalFamily a).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌) k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (p.app (Opposite.op ⦋0⦌) k) : (Δ[1] : SSet.{u}) ⟶ X) := by
  rw [sliceSquareIntervalFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge_vertex]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
  change SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p).app (Opposite.op ⦋1⦌) a.edge) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌) k) = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc,
    sliceSquareDiagramMap_boundaryEvaluation, SSet.comp_const]

lemma cospanSquareBoundary_source_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌)
      (horn₂₂.ι₀₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 0 := by
  change (horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
  apply Prod.ext <;> decide

lemma cospanSquareBoundary_source_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌)
      (horn₂₂.ι₁₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 1 := by
  change (horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]
  apply Prod.ext <;> decide

lemma sliceSquareIntervalFamily_source {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d) :
    sliceSquareIntervalFamily a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c := by
  rw [sliceSquareIntervalFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge_source]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) c) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

lemma sliceSquareIntervalFamily_target {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d) :
    sliceSquareIntervalFamily a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare d := by
  rw [sliceSquareIntervalFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge_target]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) d) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

lemma sliceSquareIntervalFamily_sourceEdge {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (sliceSquareIntervalFamily a) 0 0) =
      (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))).edge := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((sliceSquareIntervalFamily a).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)) = _
  rw [sliceSquareIntervalFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex]
  change SSet.yonedaEquiv
    (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap p).app (Opposite.op ⦋1⦌) a.edge) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)) = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_sourceEvaluation, SSet.yonedaEquiv_symm_comp,
    Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
