module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteTriangleRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedEdgeCompositionEquality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinements

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable [Small.{u} D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) {m : ℕ}
variable (τ : Fin m → K _⦋2⦌)
variable (G : ∀ j, ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i (τ j))))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i (τ j))).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i (τ j)))))

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement A D C τ G)

/-- 元の共通閉分母を、有限族の同じ追加閉分母で細分した閉実分母。 -/
def DGVerdierFiniteTriangleRefinement.commonDenominator : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x C.denominator T.s T.denominator

/-- 全実三単体に共通な、同じ閉細分分母の実 over 始頂点。 -/
def DGVerdierFiniteTriangleRefinement.commonApex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x
    (DGVerdierFiniteTriangleRefinement.commonDenominator A D C τ G T)

/-- 全ての回収三単体の始頂点は、一つの共通実閉細分頂点と厳密に一致する。 -/
lemma DGVerdierFiniteTriangleRefinement.apex_eq (j : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j))) =
      DGVerdierFiniteTriangleRefinement.commonApex A D C τ G T := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_comp_of_edge_eq A D
    (x' := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left) (y' := x)
    (T.residuals j).s T.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTriangleInitialClosed A D C (τ j) (G j))
    C.denominator.obj.hom (T.denominator_edge_eq j)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTriangleInitialClosed_edge A D C (τ j) (G j))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedThreeApex_comp A D C (τ j) (G j)
    (T.residuals j).q (T.residuals j).s (T.filler j) (T.filler_fac j)).trans
      (hc.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D
        (DGVerdierFiniteTriangleRefinement.commonDenominator A D C τ G T).obj.hom).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
