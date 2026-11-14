module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionHomotopyEdge
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionEndpointEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.ConstantBaseEndpointHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-!
概要：実際の相対円柱の終点の類を、既存の相対延長の比較同型の類と照合する。
方針：同じ可縮な延長空間内の辺の一意性を終点評価へ写す。
規約：底・初期値・元の円柱を保持する。使われ方：指定輸送路の高次比較への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
private lemma vertexIsoTransport_hom_arrow {Z : SSet.{u}} {x y x' y' : Z _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (hx : x = x') (hy : y = y') :
    Arrow.mk (cast (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x' z) hy)
      (cast (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z y) hx) e)).hom = Arrow.mk e.hom := by
  subst x' y'
  rfl

variable {A D C E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  (β : A ⟶ B) (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i)
  (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
  (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ β = SSet.const b)
  (W W' : A ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
  (g g' : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)
  (hWj : j ≫ W = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (hWj' : j ≫ W' = g' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)
local notation "X" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv
local notation "x" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv
  (Subtype.mk W (And.intro hW hWi))
local notation "y" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv
  (Subtype.mk W' (And.intro hW' hWi'))
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint p β i v hv j b hj

/-- 既存の比較同型は、可縮な延長空間での同型を終点へ写した同じ射である。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_hom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint_witnessIso p β i hi v hv j b hj
      W W' hW hW' hWi hWi' g g' hWj hWj').hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p β i hi v hv).vertexIso x y) r).hom := by
  exact vertexIsoTransport_hom_arrow
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p β i hi v hv).vertexIso x y) r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint_vertex p β i v hv j b hj W hW hWi g hWj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint_vertex p β i v hv j b hj W' hW' hWi' g' hWj')

/-- 同じ延長空間の任意の実際の辺は、既存の比較同型と同じ終点の類を持つ。 -/
lemma relativeExtensionFiberEndpoint_edge_hom_arrow (k : (X).Edge x y) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (k.map r).toTruncated) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint_witnessIso p β i hi v hv j b hj
        W W' hW hW' hWi hWi' g g' hWj hWj').hom := by
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p β i hi v hv
  have := hc.kanComplex
  have hk : SSet.Truncated.HomotopyCategory.homMk k.toTruncated = (hc.vertexIso x y).hom :=
    (hc.isTerminalVertex y).isTerminalHo.hom_ext _ _
  have hr := congrArg (fun z : (SSet.HomotopyCategory.mk x : SSet.HomotopyCategory X) ⟶
    SSet.HomotopyCategory.mk y ↦ (SSet.mapHomotopyCategory r).map z) hk
  exact (congrArg Arrow.mk hr).trans
    (relativeExtensionFiberEndpoint_witnessIso_hom_arrow p β i hi v hv j b hj
      W W' hW hW' hWi hWi' g g' hWj hWj').symm

variable (H : SSet.Homotopy W W')
  (hH : H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ β)
  (hI : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst D (Δ[1] : SSet.{u}) ≫ v)

omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] in
/-- 元の実際の円柱の終点の辺は、同じ延長空間の辺を終点で写した辺そのもの。 -/
lemma fixedExtensionEndpointHomotopy_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy p β H hH j b hj g g' hWj hWj')).edge =
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge p β i v hv hW hW' hWi hWi' H hH hI).map r).edge := by
  change SSet.yonedaEquiv (curry _) =
    (r).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionCurry p β i v hv H.h hH hI))
  rw [← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  apply uncurry_injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy_projection,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionCurry_endpoint_uncurry]

include hI in
/-- 底と初期値を保つ任意の実際の円柱は、既存の比較同型と同じ終点の類を持つ。 -/
lemma fixedExtensionEndpointHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy p β H hH j b hj g g' hWj hWj')) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint_witnessIso p β i hi v hv j b hj
        W W' hW hW' hWi hWi' g g' hWj hWj').hom := by
  apply Arrow.mk_injective _ _
  refine (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (fixedExtensionEndpointHomotopy_edge p β i v hv j b hj
      W W' hW hW' hWi hWi' g g' hWj hWj' H hH hI)).trans ?_
  exact relativeExtensionFiberEndpoint_edge_hom_arrow p β i hi v hv j b hj
    W W' hW hW' hWi hWi' g g' hWj hWj'
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge p β i v hv hW hW' hWi hWi' H hH hI)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
