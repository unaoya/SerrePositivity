module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentTransportComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionHomotopyEdge
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionEndpointEvaluation

/-!
概要：指定した輸送比較の同じ円柱を、可縮な辺 prism 延長空間の辺として保持する。
方針：底と始点を固定する円柱を戻し、終点評価後の円柱を元の合成ホモトピーと厳密に照合する。
規約：二単体も比較辺も同型類から選び直さない。
使われ方：実際の Hom 係数との高次比較を、同じ延長空間内で組み立てるための接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} (g : B.Edge a c)

/-- 元の長辺を底とする、辺 prism 全体の図式。 -/
def transportPrismBase : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ B :=
  fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ SSet.yonedaEquiv.symm g.edge

/-- 辺 prism の初期値は元の fiber の包含。 -/
def transportPrismInitial : (Δ[0] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ E :=
  snd (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a

omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] in
/-- prism の始点条件は、最初の頂点包含による厳密な初期値条件を与える。 -/
lemma transportPrism_initial_restriction (W : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ E)
    (hW : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ W = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ W = transportPrismInitial p (a := a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
  change snd Δ[0] (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ W = _
  rw [hW]
  rfl

/-- 固定した初期値の底は、元の長辺の始点への制限そのもの。 -/
lemma transportPrismInitial_projection :
    transportPrismInitial p (a := a) ≫ p =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ transportPrismBase p g := by
  rw [← transportPrism_initial_restriction p (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p g)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero p g), Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection]
  rfl

/-- 元の長辺と初期値の両方を固定した、実際の辺 prism の延長空間。 -/
def transportPrismExtensionSpace : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p (transportPrismBase p g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) (transportPrismInitial p (a := a))
    (transportPrismInitial_projection p g)

/-- この延長空間は、全ての比較と高次の境界を含めて可縮な Kan 複体。 -/
lemma transportPrismExtensionSpace_isContractibleKan :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (transportPrismExtensionSpace p g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)) _ _

/-- 元の長辺 prism の終点における底は、元の終点 c に定値。 -/
lemma transportPrismBase_endpoint :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ transportPrismBase p g = SSet.const c := by
  rw [transportPrismBase, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection p g, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_one, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 同じ prism 延長空間を終点で評価する射。 -/
def transportPrismExtensionEndpoint :
    transportPrismExtensionSpace p g ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint p _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)) c
    (transportPrismBase_endpoint p g)

variable {g} (σ : SSet.Edge.CompStruct e f g)

/-- 元の二単体の長辺 prism を、同じ延長空間の頂点として保持する。 -/
def coherentTransportLongPrismVertex : (transportPrismExtensionSpace p g) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p _ _ _ _
    ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism p σ, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_projection p σ,
      transportPrism_initial_restriction p _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_zero p σ)⟩

/-- 標準長辺 prism も、全く同じ延長空間の頂点。 -/
def standardTransportPrismVertex : (transportPrismExtensionSpace p g) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p _ _ _ _
    ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p g, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection p g,
      transportPrism_initial_restriction p _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero p g)⟩

/-- 指定された元の比較円柱そのものを表す、可縮な延長空間内の実際の辺。 -/
def coherentTransportComparisonEdge :
    (transportPrismExtensionSpace p g).Edge (coherentTransportLongPrismVertex p σ)
      (standardTransportPrismVertex p (g := g)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge p _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_projection p σ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection p g)
    (transportPrism_initial_restriction p _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_zero p σ))
    (transportPrism_initial_restriction p _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero p g))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportComparison p σ).homotopy
    (by simpa only [transportPrismBase, Category.assoc] using
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportComparison p σ).projection)
    (by simpa only [transportPrismInitial, Category.assoc] using
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportComparison p σ).initial)

/-- 延長空間の指定辺を展開すると、選んだ同じ輸送比較円柱を回収する。 -/
lemma coherentTransportComparisonEdge_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      (SSet.yonedaEquiv.symm (coherentTransportComparisonEdge p σ).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p _ _ _ (transportPrismInitial_projection p g)) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportComparison p σ).homotopy.h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge_uncurry _ _ _ _ _ _ _ _ _ _ _ _

/-- 終点で評価した同じ辺の円柱は、既存の合成比較ホモトピーの円柱そのもの。 -/
lemma coherentTransportComparisonEdge_endpoint_uncurry :
    uncurry (SSet.yonedaEquiv.symm (coherentTransportComparisonEdge p σ).edge ≫
      transportPrismExtensionEndpoint p g) =
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionHomotopy p σ).h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p c
  rw [transportPrismExtensionEndpoint, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeExtensionFiberEndpoint_uncurry,
    coherentTransportComparisonEdge_uncurry,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionHomotopy_projection]

/-- 同じ長辺 prism の頂点を終点で評価すると、元の二段階輸送の関手頂点になる。 -/
lemma coherentTransportLongPrismVertex_endpoint :
    (transportPrismExtensionEndpoint p g).app _ (coherentTransportLongPrismVertex p σ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f) := by
  dsimp only [transportPrismExtensionEndpoint, coherentTransportLongPrismVertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint_vertex p (transportPrismBase p g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) (transportPrismInitial p (a := a))
    (transportPrismInitial_projection p g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)) c
    (transportPrismBase_endpoint p g) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism p σ)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_projection p σ)
    (transportPrism_initial_restriction p _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_zero p σ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_one p σ)

/-- 標準 prism の頂点の終点評価は、元の長辺輸送の関手頂点。 -/
lemma standardTransportPrismVertex_endpoint :
    (transportPrismExtensionEndpoint p g).app _ (standardTransportPrismVertex p (g := g)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p g) := by
  dsimp only [transportPrismExtensionEndpoint, standardTransportPrismVertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint_vertex p (transportPrismBase p g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) (transportPrismInitial p (a := a))
    (transportPrismInitial_projection p g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)) c
    (transportPrismBase_endpoint p g) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p g) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection p g)
    (transportPrism_initial_restriction p _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero p g))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p g) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_one p g)

/-- 両端の表示を揃えた、同じ指定比較辺の終点での像。 -/
def coherentTransportComparisonEndpointEdge :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c)).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p g)) :=
  { edge := ((coherentTransportComparisonEdge p σ).map (transportPrismExtensionEndpoint p g)).edge
    src_eq := ((coherentTransportComparisonEdge p σ).map
      (transportPrismExtensionEndpoint p g)).src_eq.trans
        (coherentTransportLongPrismVertex_endpoint p σ)
    tgt_eq := ((coherentTransportComparisonEdge p σ).map
      (transportPrismExtensionEndpoint p g)).tgt_eq.trans
        (standardTransportPrismVertex_endpoint p (g := g)) }

/-- 終点での像は、元の合成比較の実際の関手辺そのもの。 -/
lemma coherentTransportComparisonEndpointEdge_eq :
    (coherentTransportComparisonEndpointEdge p σ).toTruncated =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionHomotopy p σ) := by
  apply SSet.Truncated.Edge.ext
  change ((coherentTransportComparisonEdge p σ).map (transportPrismExtensionEndpoint p g)).edge =
    SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionHomotopy p σ).h)
  apply (SSet.yonedaEquiv (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c))).symm.injective
  rw [Equiv.symm_apply_apply]
  change SSet.yonedaEquiv.symm
    ((transportPrismExtensionEndpoint p g).app (Opposite.op ⦋1⦌)
      (coherentTransportComparisonEdge p σ).edge) = _
  rw [← SSet.yonedaEquiv_symm_comp]
  apply uncurry_injective
  rw [uncurry_curry, coherentTransportComparisonEdge_endpoint_uncurry]

/-- 指定辺の終点での像の類は、境界経路に使用する元の合成同型の順方向の射。 -/
lemma coherentTransportComparisonEndpointEdge_homMk :
    SSet.Truncated.HomotopyCategory.homMk
        (coherentTransportComparisonEndpointEdge p σ).toTruncated =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionIso p σ).hom := by
  rw [coherentTransportComparisonEndpointEdge_eq]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
