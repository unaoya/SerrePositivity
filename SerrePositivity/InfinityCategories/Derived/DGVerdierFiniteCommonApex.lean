module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierFiniteEdgeRefinement
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdgeCompositionEquality
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofRefinements

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable {C : DGVerdierDiagramVertexCone A D P x f} {m : ℕ} {e : Fin m → K _⦋1⦌}
variable (T : DGVerdierFiniteEdgeRefinement A D C e)

/-- 元の共通閉分母を同じ追加閉分母で細分した、一つの閉実分母。 -/
def DGVerdierFiniteEdgeRefinement.commonDenominator : DGClosedVerdierDenominators A D P x :=
  dgClosedRoofRefine A D P x C.denominator T.s T.denominator

/-- 全辺に共通する、同じ閉細分分母の実 over 頂点。 -/
def DGVerdierFiniteEdgeRefinement.commonApex : (dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  dgClosedVerdierDenominatorVertex A D P x T.commonDenominator

/-- 各辺の新 apex は、同じ一つの共通閉細分頂点と厳密に一致する。 -/
lemma DGVerdierFiniteEdgeRefinement.apex_eq (i : Fin m) :
    (T.refinements i).apex = T.commonApex := by
  apply Subtype.ext
  apply roofPointSliceVertexEdge_injective
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
  let g := dgSimplexClosedDiagonal A D
    (dgLastHornCanonicalFace (dgVerdierDiagramEdgeHorn A D C (e i)) 1 (by decide))
  have hg : (dgClosedEdge A D g).edge = (dgClosedEdge A D C.denominator.obj.hom).edge :=
    (dgSimplexClosedDiagonal_edge A D
      (dgLastHornCanonicalFace (dgVerdierDiagramEdgeHorn A D C (e i)) 1 (by decide))).symm.trans
        (dgVerdierDiagramInitialDiagonal_edge A D C (e i))
  have hc := dgClosedEdge_comp_of_edge_eq A D
    (x' := ForgetEnrichment.to (Complex A) C.denominator.obj.left) (y' := x)
    (T.refinements i).s T.s g C.denominator.obj.hom (T.denominator_edge_eq i) hg
  exact (T.refinements i).apex_edge.trans (hc.trans
    (dgClosedOverVertex_edge A D T.commonDenominator.obj.hom).symm)

/-- 全て同じ共通実 apex から、各指定辺の始点へ向かう実脚。 -/
def DGVerdierFiniteEdgeRefinement.sourceLeg (i : Fin m) :
    Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet))
      T.commonApex (f.app _ (K.δ 1 (e i))) where
  edge := (T.refinements i).sourceLeg.edge
  src_eq := (T.refinements i).sourceLeg.src_eq.trans (DGVerdierFiniteEdgeRefinement.apex_eq A D T i)
  tgt_eq := (T.refinements i).sourceLeg.tgt_eq

/-- 全て同じ共通実 apex から、各指定辺の終点へ向かう実脚。 -/
def DGVerdierFiniteEdgeRefinement.targetLeg (i : Fin m) :
    Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet))
      T.commonApex (f.app _ (K.δ 0 (e i))) where
  edge := (T.refinements i).targetLeg.edge
  src_eq := (T.refinements i).targetLeg.src_eq.trans (DGVerdierFiniteEdgeRefinement.apex_eq A D T i)
  tgt_eq := (T.refinements i).targetLeg.tgt_eq

/-- 同じ共通 apex からの各二脚と指定図式辺は、同じ実合成二単体を持つ。 -/
def DGVerdierFiniteEdgeRefinement.compStruct (i : Fin m) :
    Truncated.Edge.CompStruct
      (DGVerdierFiniteEdgeRefinement.sourceLeg A D T i)
      ((edgeOfSimplex (e i)).map ((truncation 2).map f))
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
    (dgVerdierOverSource A D P x).app _
      (DGVerdierFiniteEdgeRefinement.sourceLeg A D T i).edge ∈ dgVerdierEdges A D P :=
  (T.refinements i).sourceLeg_mem

/-- 共通始頂点から各辺の終点への脚の始域射影も実分母。 -/
lemma DGVerdierFiniteEdgeRefinement.targetLeg_mem (i : Fin m) :
    (dgVerdierOverSource A D P x).app _
      (DGVerdierFiniteEdgeRefinement.targetLeg A D T i).edge ∈ dgVerdierEdges A D P :=
  (T.refinements i).targetLeg_mem

end SerrePositivity.InfinityCategories
