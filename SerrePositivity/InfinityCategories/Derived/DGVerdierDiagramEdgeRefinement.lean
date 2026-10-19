module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRefinedTriangle
public import SerrePositivity.InfinityCategories.Derived.TriangleConeOfFace
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverRefinement

/-! # 実図式辺に対する追加閉分母と実分母部分圏内の辺錐

概要：指定辺ごとの細分データから、実分母始頂点・二脚・元の辺の合成二単体を供給する。
方針：既供給の実充填を同じ over 二単体として持ち上げ、その三面を回収する。
規約：辺ごとの存在であり有限図式の共通錐を主張しない。使われ方：有限同時細分の界面。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)

/-- 指定実図式辺の同じ閉始点細分と、実ホーン全体の充填データ。 -/
structure DGVerdierDiagramEdgeRefinement where
  q : D
  s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
    ((HornData.knownData (dgVerdierDiagramEdgeHorn A D C e)).obj 0)
  denominator : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P
  filler : Δ[3] ⟶ dgNerve A D
  fac : (horn 3 3).ι ≫ filler =
    dgLastHornSourceRefinement (dgVerdierDiagramEdgeHorn A D C e) q s

variable [Small.{u} D] [IsDGPretriangulated A D]
variable (R : DGVerdierDiagramEdgeRefinement A D C e)

/-- 同じ細分四面体から構成した、実分母部分圏の実二単体。 -/
def DGVerdierDiagramEdgeRefinement.triangle : (dgVerdierOver A D P x : SSet) _⦋2⦌ :=
  dgVerdierDiagramRefinedTriangle A D C e R.q R.s R.denominator R.filler R.fac

/-- 実分母部分圏内の三角形の零面は、元の指定実図式辺。 -/
lemma DGVerdierDiagramEdgeRefinement.triangle_face0 :
    (dgVerdierOver A D P x : SSet).δ 0 R.triangle = f.app _ e :=
  dgVerdierDiagramRefinedTriangle_face0 A D C e R.q R.s R.denominator R.filler R.fac

/-- 細分始頂点は、同じ実分母部分圏内の実頂点。 -/
def DGVerdierDiagramEdgeRefinement.apex : (dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  triangleConeApex R.triangle

/-- 細分した実始頂点の分母辺は、元の対角閉射と同じ追加閉分母との合成。 -/
lemma DGVerdierDiagramEdgeRefinement.apex_edge :
    (roofPointSliceVertexEdge
      ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) R.apex.val).edge =
      (dgClosedEdge A D (R.s ≫ dgSimplexClosedDiagonal A D
        (dgLastHornCanonicalFace (dgVerdierDiagramEdgeHorn A D C e) 1 (by decide)))).edge :=
  (dgVerdierDiagramRefinedApex_edge A D C e R.q R.s R.filler R.fac).trans
    (dgSimplexSourceRefinement_face1_comp A D
      (dgLastHornCanonicalFace (dgVerdierDiagramEdgeHorn A D C e) 1 (by decide)) R.q R.s)

/-- 新始頂点から元の指定図式辺の始点へ向かう、実分母部分圏内の実脚。 -/
def DGVerdierDiagramEdgeRefinement.sourceLeg :
    Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet))
      R.apex (f.app _ (K.δ 1 e)) :=
  triangleConeLegSource R.triangle ((edgeOfSimplex e).map ((truncation 2).map f))
    R.triangle_face0

/-- 同じ新始頂点から元の指定図式辺の終点へ向かう、実分母部分圏内の実脚。 -/
def DGVerdierDiagramEdgeRefinement.targetLeg :
    Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet))
      R.apex (f.app _ (K.δ 0 e)) :=
  triangleConeLegTarget R.triangle ((edgeOfSimplex e).map ((truncation 2).map f))
    R.triangle_face0

/-- 回収した二脚と元の指定実図式辺は、同じ実二単体で合成整合性を持つ。 -/
def DGVerdierDiagramEdgeRefinement.compStruct :
    Truncated.Edge.CompStruct R.sourceLeg ((edgeOfSimplex e).map ((truncation 2).map f))
      R.targetLeg :=
  triangleConeCompStruct R.triangle ((edgeOfSimplex e).map ((truncation 2).map f))
    R.triangle_face0

/-- 実合成二単体の台は、同じ閉細分四面体から回収・持ち上げた三角形そのもの。 -/
lemma DGVerdierDiagramEdgeRefinement.compStruct_simplex :
    R.compStruct.simplex = R.triangle := rfl

/-- 回収した始点側の脚の始域射影も、同じ指定集合の実 Verdier 分母。 -/
lemma DGVerdierDiagramEdgeRefinement.sourceLeg_mem :
    (dgVerdierOverSource A D P x).app _ R.sourceLeg.edge ∈ dgVerdierEdges A D P :=
  dgVerdierOverSource_edge_mem A D P x R.sourceLeg.edge

/-- 回収した終点側の脚の始域射影も、同じ指定集合の実 Verdier 分母。 -/
lemma DGVerdierDiagramEdgeRefinement.targetLeg_mem :
    (dgVerdierOverSource A D P x).app _ R.targetLeg.edge ∈ dgVerdierEdges A D P :=
  dgVerdierOverSource_edge_mem A D P x R.targetLeg.edge

/-- 任意の指定実図式辺には、追加閉分母後の実分母部分圏内の辺錐データが存在する。 -/
theorem dgVerdierDiagramEdgeRefinement_nonempty :
    Nonempty (DGVerdierDiagramEdgeRefinement A D C e) := by
  obtain ⟨q, s, hs, F, hF⟩ := dgVerdierDiagramEdge_exists_refinedFiller A D C e
  exact ⟨⟨q, s, hs, F, hF⟩⟩

end SerrePositivity.InfinityCategories
