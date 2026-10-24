module
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramFixed
public import SerrePositivity.InfinityCategories.Stable.FunctorEdgeArrowFamily
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
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
namespace SerrePositivity.InfinityCategories

lemma sliceSquareDiagramMap_boundaryEvaluation {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) (k : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    sliceSquareDiagramMap p ≫ evaluateFunctorAt (Y := X)
      (cospanSquareBoundary.app (Opposite.op ⦋0⦌) k) =
      SSet.const (p.app (Opposite.op ⦋0⦌) k) := by
  rw [← stable_pre_evaluateFunctorAt (X := X) cospanSquareBoundary k,
    ← Category.assoc, sliceSquareDiagramMap_fixed, SSet.const_comp,
    evaluateFunctorAt_functorVertex]

def sliceSquareIntervalFamily {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (sliceOver p)) c d) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  arrowFamilyOfFunctorEdge (a.map ((truncation 2).map (sliceSquareDiagramMap p)))

lemma sliceSquareIntervalFamily_boundary {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (sliceOver p)) c d)
    (k : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    (sliceSquareIntervalFamily a).app (Opposite.op ⦋0⦌)
      (cospanSquareBoundary.app (Opposite.op ⦋0⦌) k) =
      functorVertex (SSet.const (p.app (Opposite.op ⦋0⦌) k) : (Δ[1] : SSet.{u}) ⟶ X) := by
  rw [sliceSquareIntervalFamily, arrowFamilyOfFunctorEdge_vertex]
  apply congrArg functorVertex
  change SSet.yonedaEquiv.symm ((sliceSquareDiagramMap p).app (Opposite.op ⦋1⦌) a.edge) ≫
    evaluateFunctorAt (Y := X) (cospanSquareBoundary.app (Opposite.op ⦋0⦌) k) = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc,
    sliceSquareDiagramMap_boundaryEvaluation, SSet.comp_const]

lemma cospanSquareBoundary_source_right :
    cospanSquareBoundary.app (Opposite.op ⦋0⦌)
      (horn₂₂.ι₀₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 0 := by
  change (horn₂₂.ι₀₂ ≫ cospanSquareBoundary).app _ _ = _
  rw [cospanSquareBoundary_rightEdge]
  apply Prod.ext <;> decide

lemma cospanSquareBoundary_source_top :
    cospanSquareBoundary.app (Opposite.op ⦋0⦌)
      (horn₂₂.ι₁₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 1 := by
  change (horn₂₂.ι₁₂ ≫ cospanSquareBoundary).app _ _ = _
  rw [cospanSquareBoundary_topEdge]
  apply Prod.ext <;> decide

lemma sliceSquareIntervalFamily_source {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (sliceOver p)) c d) :
    sliceSquareIntervalFamily a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      coneSquare c := by
  rw [sliceSquareIntervalFamily, arrowFamilyOfFunctorEdge_source]
  change (functorVertexEquiv _ _).symm
    ((sliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) c) = _
  rw [sliceSquareDiagramMap_vertex]
  exact (functorVertexEquiv _ _).symm_apply_apply _

lemma sliceSquareIntervalFamily_target {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (sliceOver p)) c d) :
    sliceSquareIntervalFamily a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      coneSquare d := by
  rw [sliceSquareIntervalFamily, arrowFamilyOfFunctorEdge_target]
  change (functorVertexEquiv _ _).symm
    ((sliceSquareDiagramMap p).app (Opposite.op ⦋0⦌) d) = _
  rw [sliceSquareDiagramMap_vertex]
  exact (functorVertexEquiv _ _).symm_apply_apply _

lemma sliceSquareIntervalFamily_sourceEdge {X : SSet.{u}}
    {p : (horn 2 2 : SSet.{u}) ⟶ X} {c d : JoinCone p}
    (a : Truncated.Edge (X := (truncation 2).obj (sliceOver p)) c d) :
    intervalFunctorVertexEdge (squareVertex (sliceSquareIntervalFamily a) 0 0) =
      (a.map ((truncation 2).map (sliceOverProjection p))).edge := by
  change intervalFunctorVertexEdge ((sliceSquareIntervalFamily a).app (Opposite.op ⦋0⦌)
    (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)) = _
  rw [sliceSquareIntervalFamily, arrowFamilyOfFunctorEdge_vertex,
    intervalFunctorVertexEdge_functorVertex]
  change SSet.yonedaEquiv
    (SSet.yonedaEquiv.symm ((sliceSquareDiagramMap p).app (Opposite.op ⦋1⦌) a.edge) ≫
      evaluateFunctorAt (Y := X) (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)) = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc,
    sliceSquareDiagramMap_sourceEvaluation, SSet.yonedaEquiv_symm_comp,
    Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories
