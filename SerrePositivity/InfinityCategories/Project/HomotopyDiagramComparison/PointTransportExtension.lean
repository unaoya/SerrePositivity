module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTransportPointComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionVertexEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ContractibleEdgeEvaluation

/-!
概要：点評価した元の輸送比較円柱を、同じ根辺の固定延長空間へ戻す。
方針：元の始点と底を固定した実際の長辺・標準辺を頂点として保持する。
規約：同じ二単体と同じ比較円柱を使う。使われ方：標準長辺の正準比較の native な同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma pointTransportInitial_eq :
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 := by
  apply SSet.yonedaEquiv.injective
  decide

variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} (g : B.Edge a c)
  (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌)
local notation "β" => SSet.yonedaEquiv.symm g.edge
local notation "i" => stdSimplex.δ (1 : Fin 2)
local notation "w" => SSet.yonedaEquiv.symm v.val
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p g) v

/-- 同じ標準辺の始点は、元の fiber の指定頂点。 -/
lemma standardTransportPoint_initial : i ≫ V = w := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge_diagram]
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge p g v).δ_one_yonedaEquiv_symm

/-- 点の標準辺も、元の底の辺を厳密に被覆する。 -/
lemma standardTransportPoint_projection : V ≫ p = β :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation_projection p _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection p g) v

/-- 同じ始点を固定するための底の整合性。 -/
lemma pointTransportExtension_initial_base : w ≫ p = i ≫ β :=
  (congrArg (fun z ↦ z ≫ p) (standardTransportPoint_initial p g v).symm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ i ≫ z) (standardTransportPoint_projection p g v)))

local notation "hv" => pointTransportExtension_initial_base p g v

/-- 元の根辺と同じ点の初期値を固定する、実際の辺の延長空間。 -/
def pointTransportExtensionSpace : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i w hv

/-- この延長空間は、全高次の比較を含めて可縮な Kan 複体。 -/
lemma pointTransportExtensionSpace_isContractibleKan :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (pointTransportExtensionSpace p g v) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan
  rw [pointTransportInitial_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne 1

/-- 元の標準 prism の同じ点評価を、この空間の頂点にする。 -/
def standardTransportPointExtensionVertex : (pointTransportExtensionSpace p g v) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i w hv
    ⟨V, standardTransportPoint_projection p g v, standardTransportPoint_initial p g v⟩

/-- 全延長を同じ根辺の終点で評価する射。 -/
def pointTransportExtensionEndpoint : pointTransportExtensionSpace p g v ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget p β i w hv (𝟙 Δ[1]) g (Category.id_comp β)

variable {g} (σ : SSet.Edge.CompStruct e f g)
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism p σ) v
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointComparisonHomotopy p σ v

/-- 元の三角形の長辺の始点も、同じ元の fiber 頂点。 -/
lemma coherentTransportLongPoint_initial : i ≫ W = w := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismPointEdge_diagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism p σ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_zero p σ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_one p σ)]
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleDiagonalPointEdge p σ v).δ_one_yonedaEquiv_symm

/-- 同じ三角形の長辺も、元の底の根辺を厳密に被覆する。 -/
lemma coherentTransportLongPoint_projection : W ≫ p = β :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation_projection p _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_projection p σ) v

/-- 元の三角形の実際の長辺を、同じ根辺空間の頂点として保持する。 -/
def coherentTransportLongPointExtensionVertex : (pointTransportExtensionSpace p g v) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i w hv
    ⟨W, coherentTransportLongPoint_projection p v σ, coherentTransportLongPoint_initial p v σ⟩

/-- 点評価した元の円柱は、最初の面の初期図式を全時刻で固定する。 -/
lemma coherentTransportPointComparisonHomotopy_initial_face :
    (i ▷ (Δ[1] : SSet.{u})) ≫ (H).h = fst (Δ[0] : SSet.{u}) Δ[1] ≫ w := by
  rw [pointTransportInitial_eq]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointComparisonHomotopy_initial p σ v

/-- 元の点比較円柱を同じ延長空間の実際の辺として保持する。 -/
def coherentTransportPointComparisonExtensionEdge :
    (pointTransportExtensionSpace p g v).Edge (coherentTransportLongPointExtensionVertex p v σ)
      (standardTransportPointExtensionVertex p g v) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge p β i w hv
    (coherentTransportLongPoint_projection p v σ) (standardTransportPoint_projection p g v)
    (coherentTransportLongPoint_initial p v σ) (standardTransportPoint_initial p g v)
    H (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointComparisonHomotopy_projection p σ v)
    (coherentTransportPointComparisonHomotopy_initial_face p v σ)

/-- 同じ点比較辺を展開しても、元の円柱を回収する。 -/
lemma coherentTransportPointComparisonExtensionEdge_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm
      (coherentTransportPointComparisonExtensionEdge p v σ).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i w hv) = (H).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge_uncurry _ _ _ _ _ _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
