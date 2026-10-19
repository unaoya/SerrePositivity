module
public import SerrePositivity.InfinityCategories.Derived.DGTriangleRefinementClosedDiagonal
public import SerrePositivity.InfinityCategories.Derived.DGLastHornCanonicalFaces
public import SerrePositivity.InfinityCategories.Derived.DGVerdierLastHornDenominator

/-! # 実分母図式ホーンの元の始頂点の対角分母辺

概要：面 023 の対角辺 03 を、元の実 over 始頂点の指定分母辺と厳密に同定する。
方針：指定一面の等式と実 over 三角形の始脚の公式を使う。
規約：一次単体そのものの一致。使われ方：追加閉細分後の始頂点の実分母性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : Set D) (x : D)
variable {d a b : (dgVerdierOver A D P x : SSet.{max u v}) _⦋0⦌}
variable (u : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) d a)
variable (e : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) a b)
variable (w : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) d b)

/-- 面 023 の対角実辺 03 は、元の始頂点の指定分母辺そのもの。 -/
lemma dgVerdierConeInitialDiagonal_edge :
    (dgNerve A D).δ 1 (dgLastHornCanonicalFace
      (dgVerdierConeEdgeHorn A D P x u e w) 1 (by decide)) =
      (roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) d.val).edge := by
  let z := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let H := dgVerdierConeEdgeHorn A D P x u e w
  let W := w.map ((truncation 2).map (dgVerdierOver A D P x).ι)
  have hface : H.app _ (horn.face 3 1 (by decide)) =
      (SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceTriangle z W.edge) :=
    (SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 1 (by decide)) H).symm.trans
      (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
        (dgVerdierConeEdgeHorn_face1 A D P x u e w))
  exact (congrArg ((dgNerve A D).δ (1 : Fin 3))
    ((dgLastHornCanonicalFace_eq H 1 (by decide)).trans hface)).trans
      ((SSet.stdSimplex.yonedaEquiv_δ_comp (roofPointSliceTriangle z W.edge) 1).symm.trans
        ((roofPointSliceTriangle_leg z W.edge 1).trans
          (congrArg (fun v => (roofPointSliceVertexEdge z v).edge) W.src_eq)))

/-- 元の始頂点の同じ対角実辺 03 は、指定された実 Verdier 分母。 -/
lemma dgVerdierConeInitialDiagonal_mem :
    (dgNerve A D).δ 1 (dgLastHornCanonicalFace
      (dgVerdierConeEdgeHorn A D P x u e w) 1 (by decide)) ∈ dgVerdierEdges A D P :=
  (congrArg (fun z => z ∈ dgVerdierEdges A D P)
    (dgVerdierConeInitialDiagonal_edge A D P x u e w)).mpr (dgVerdierOverVertex_mem A D P x d)

variable {K : SSet.{max u v}} {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}

/-- 任意の実図式辺ホーンの元の対角 03 も、同じ指定集合に関する実分母。 -/
lemma dgVerdierDiagramInitialDiagonal_mem (C : DGVerdierDiagramVertexCone A D P x f)
    (a : K _⦋1⦌) :
    (dgNerve A D).δ 1 (dgLastHornCanonicalFace
      (dgVerdierDiagramEdgeHorn A D C a) 1 (by decide)) ∈ dgVerdierEdges A D P :=
  dgVerdierConeInitialDiagonal_mem A D P x (C.leg (K.δ 1 a))
    ((edgeOfSimplex a).map ((truncation 2).map f)) (C.leg (K.δ 0 a))

end SerrePositivity.InfinityCategories
