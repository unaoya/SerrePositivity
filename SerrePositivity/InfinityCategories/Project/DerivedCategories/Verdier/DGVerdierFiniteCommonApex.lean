module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteEdgeRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedEdgeCompositionEquality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinements

/-! # 有限同時細分の共通実分母始頂点と実辺錐

概要：有限族の全新 apex を同じ閉細分頂点へ同定し、全辺錐を同じ始頂点へ揃える。
方針：追加分母と元の対角分母の実辺の厳密一致を閉合成へ渡し、実 over 頂点を判定する。
規約：頂点に付随する脚の辺間一致は別工程。使われ方：有限実図式の共通錐の組み立て。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable {C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f} {m : ℕ} {e : Fin m → K _⦋1⦌}
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement A D C e)

/-- 元の共通閉分母を同じ追加閉分母で細分した、一つの閉実分母。 -/
def DGVerdierFiniteEdgeRefinement.commonDenominator : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x C.denominator T.s T.denominator

/-- 全辺に共通する、同じ閉細分分母の実 over 頂点。 -/
def DGVerdierFiniteEdgeRefinement.commonApex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x T.commonDenominator

/-- 各辺の新 apex は、同じ一つの共通閉細分頂点と厳密に一致する。 -/
lemma DGVerdierFiniteEdgeRefinement.apex_eq (i : Fin m) :
    (T.refinements i).apex = T.commonApex := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexClosedDiagonal A D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C (e i)) 1 (by decide))
  have hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D C.denominator.obj.hom).edge :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexClosedDiagonal_edge A D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C (e i)) 1 (by decide))).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramInitialDiagonal_edge A D C (e i))
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_comp_of_edge_eq A D
    (x' := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left) (y' := x)
    (T.refinements i).s T.s g C.denominator.obj.hom (T.denominator_edge_eq i) hg
  exact (T.refinements i).apex_edge.trans (hc.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D T.commonDenominator.obj.hom).symm)

/-- 全て同じ共通実 apex から、各指定辺の始点へ向かう実脚。 -/
def DGVerdierFiniteEdgeRefinement.sourceLeg (i : Fin m) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
      T.commonApex (f.app _ (K.δ 1 (e i))) where
  edge := (T.refinements i).sourceLeg.edge
  src_eq := (T.refinements i).sourceLeg.src_eq.trans (DGVerdierFiniteEdgeRefinement.apex_eq A D T i)
  tgt_eq := (T.refinements i).sourceLeg.tgt_eq

/-- 全て同じ共通実 apex から、各指定辺の終点へ向かう実脚。 -/
def DGVerdierFiniteEdgeRefinement.targetLeg (i : Fin m) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
      T.commonApex (f.app _ (K.δ 0 (e i))) where
  edge := (T.refinements i).targetLeg.edge
  src_eq := (T.refinements i).targetLeg.src_eq.trans (DGVerdierFiniteEdgeRefinement.apex_eq A D T i)
  tgt_eq := (T.refinements i).targetLeg.tgt_eq

/-- 同じ共通 apex からの各二脚と指定図式辺は、同じ実合成二単体を持つ。 -/
def DGVerdierFiniteEdgeRefinement.compStruct (i : Fin m) :
    Truncated.Edge.CompStruct
      (DGVerdierFiniteEdgeRefinement.sourceLeg A D T i)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (e i)).map ((truncation 2).map f))
      (DGVerdierFiniteEdgeRefinement.targetLeg A D T i) where
  simplex := (T.refinements i).compStruct.simplex
  d₂ := (T.refinements i).compStruct.d₂
  d₀ := (T.refinements i).compStruct.d₀
  d₁ := (T.refinements i).compStruct.d₁

/-- 共通始頂点へ揃えた実合成二単体は、元の同時充填から回収した二単体そのもの。 -/
lemma DGVerdierFiniteEdgeRefinement.compStruct_simplex (i : Fin m) :
    (DGVerdierFiniteEdgeRefinement.compStruct A D T i).simplex = (T.refinements i).triangle := rfl

/-- 共通始頂点から各辺の始点への脚の始域射影も実分母。 -/
lemma DGVerdierFiniteEdgeRefinement.sourceLeg_mem (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app _
      (DGVerdierFiniteEdgeRefinement.sourceLeg A D T i).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  (T.refinements i).sourceLeg_mem

/-- 共通始頂点から各辺の終点への脚の始域射影も実分母。 -/
lemma DGVerdierFiniteEdgeRefinement.targetLeg_mem (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app _
      (DGVerdierFiniteEdgeRefinement.targetLeg A D T i).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  (T.refinements i).targetLeg_mem

end SerrePositivity.InfinityCategories.Project.DerivedCategories
