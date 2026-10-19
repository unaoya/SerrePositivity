module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierFiniteTriangleRefinement
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdgeCompositionEquality
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofRefinements

/-! # 二単体有限族の実三単体の共通閉分母 apex

概要：全ての回収三単体の新始頂点は、同じ追加閉分母で細分した一つの実頂点と厳密に一致。
方針：元の対角閉分母と追加閉分母の実辺の等式を合成し、over 頂点の単射性を使う。
規約：面や頂点脚の整合性は別工程。使われ方：有限高次共通錐の共通始点。
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
variable [Small.{u} D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) {m : ℕ}
variable (τ : Fin m → K _⦋2⦌)
variable (G : ∀ j, ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i (τ j))))
  ((edgeOfSimplex (K.δ i (τ j))).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i (τ j)))))

variable [IsDGPretriangulated A D]
variable (T : DGVerdierFiniteTriangleRefinement A D C τ G)

/-- 元の共通閉分母を、有限族の同じ追加閉分母で細分した閉実分母。 -/
def DGVerdierFiniteTriangleRefinement.commonDenominator : DGClosedVerdierDenominators A D P x :=
  dgClosedRoofRefine A D P x C.denominator T.s T.denominator

/-- 全実三単体に共通な、同じ閉細分分母の実 over 始頂点。 -/
def DGVerdierFiniteTriangleRefinement.commonApex : (dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  dgClosedVerdierDenominatorVertex A D P x
    (DGVerdierFiniteTriangleRefinement.commonDenominator A D C τ G T)

/-- 全ての回収三単体の始頂点は、一つの共通実閉細分頂点と厳密に一致する。 -/
lemma DGVerdierFiniteTriangleRefinement.apex_eq (j : Fin m) :
    (dgVerdierOver A D P x : SSet).δ 1 ((dgVerdierOver A D P x : SSet).δ 1
      ((dgVerdierOver A D P x : SSet).δ 1
        (DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j))) =
      DGVerdierFiniteTriangleRefinement.commonApex A D C τ G T := by
  apply Subtype.ext
  apply roofPointSliceVertexEdge_injective
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
  have hc := dgClosedEdge_comp_of_edge_eq A D
    (x' := ForgetEnrichment.to (Complex A) C.denominator.obj.left) (y' := x)
    (T.residuals j).s T.s (dgVerdierTriangleInitialClosed A D C (τ j) (G j))
    C.denominator.obj.hom (T.denominator_edge_eq j)
    (dgVerdierTriangleInitialClosed_edge A D C (τ j) (G j))
  exact (dgVerdierDiagramRefinedThreeApex_comp A D C (τ j) (G j)
    (T.residuals j).q (T.residuals j).s (T.filler j) (T.filler_fac j)).trans
      (hc.trans (dgClosedOverVertex_edge A D
        (DGVerdierFiniteTriangleRefinement.commonDenominator A D C τ G T).obj.hom).symm)

end SerrePositivity.InfinityCategories
