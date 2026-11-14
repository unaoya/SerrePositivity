module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGTriangleRefinementClosedDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornCanonicalFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGVerdierLastHornDenominator

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] (P : Set D) (x : D)
variable {d a b : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋0⦌}
variable (u : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) d a)
variable (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) a b)
variable (w : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) d b)

/-- 面 023 の対角実辺 03 は、元の始頂点の指定分母辺そのもの。 -/
lemma dgVerdierConeInitialDiagonal_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn A D P x u e w) 1 (by decide)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) d.val).edge := by
  let z := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn A D P x u e w
  let W := w.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)
  have hface : H.app _ (horn.face 3 1 (by decide)) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle z W.edge) :=
    (SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 1 (by decide)) H).symm.trans
      (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn_face1 A D P x u e w))
  exact (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ (1 : Fin 3))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_eq H 1 (by decide)).trans hface)).trans
      ((SSet.stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle z W.edge) 1).symm.trans
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg z W.edge 1).trans
          (congrArg (fun v => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge z v).edge) W.src_eq)))

/-- 元の始頂点の同じ対角実辺 03 は、指定された実 Verdier 分母。 -/
lemma dgVerdierConeInitialDiagonal_mem :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn A D P x u e w) 1 (by decide)) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  (congrArg (fun z => z ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (dgVerdierConeInitialDiagonal_edge A D P x u e w)).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertex_mem A D P x d)

variable {K : SSet.{max u v}} {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}

/-- 任意の実図式辺ホーンの元の対角 03 も、同じ指定集合に関する実分母。 -/
lemma dgVerdierDiagramInitialDiagonal_mem (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)
    (a : K _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C a) 1 (by decide)) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  dgVerdierConeInitialDiagonal_mem A D P x (C.leg (K.δ 1 a))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a).map ((truncation 2).map f)) (C.leg (K.δ 0 a))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
