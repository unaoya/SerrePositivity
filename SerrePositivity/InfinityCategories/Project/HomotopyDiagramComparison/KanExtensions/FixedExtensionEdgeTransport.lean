module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionEndpointEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PrismCylinderParameter
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：固定延長の全族を指定した辺へ制限し、その両端の輸送比較と自然性を構成する。
方針：同じ全族から両端の fiber への射を取り、全係数の prism 輸送比較を適用する。
規約：延長空間の任意の実際の辺を使う。使われ方：左三角形の終点比較の合成式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {K D E B : SSet.{u}} (p : E ⟶ B) (β : K ⟶ B)
  (i : D ⟶ K) (v : D ⟶ E) (hv : v ≫ p = i ≫ β) (k : (Δ[1] : SSet.{u}) ⟶ K)
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv

/-- 元の全延長の同じ族を、指定した辺へ制限した prism。 -/
def fixedExtensionEdgePrism : (Δ[1] : SSet.{u}) ⊗ S ⟶ E :=
  (k ▷ S) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv)

variable {a b : B _⦋0⦌} (e : B.Edge a b) (hk : k ≫ β = SSet.yonedaEquiv.symm e.edge)

include hk in
/-- 同じ全延長の辺 prism は、指定した底の辺を厳密に被覆する。 -/
lemma fixedExtensionEdgePrism_projection :
    fixedExtensionEdgePrism p β i v hv k ≫ p =
      fst (Δ[1] : SSet.{u}) S ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [fixedExtensionEdgePrism, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc, hk]

include hk in
/-- 辺 prism の始点の族は、底の同じ始点に定値な射影を持つ。 -/
lemma fixedExtensionEdgePrism_zero_base :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 S ≫ fixedExtensionEdgePrism p β i v hv k) ≫ p = SSet.const a := by
  rw [Category.assoc, fixedExtensionEdgePrism_projection p β i v hv k e hk]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_zero e.edge).trans (congrArg (fun z ↦ (SSet.const z : S ⟶ B)) e.src_eq)

include hk in
/-- 終点の族も、同じ指定終点に定値な射影を持つ。 -/
lemma fixedExtensionEdgePrism_one_base :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S ≫ fixedExtensionEdgePrism p β i v hv k) ≫ p = SSet.const b := by
  rw [Category.assoc, fixedExtensionEdgePrism_projection p β i v hv k e hk]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : S ⟶ B)) e.tgt_eq)

/-- 指定した辺の始点で評価した、全延長から始点 fiber への同じ族。 -/
def fixedExtensionEdgeSource : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 S ≫ fixedExtensionEdgePrism p β i v hv k)
    (fixedExtensionEdgePrism_zero_base p β i v hv k e hk)

/-- 指定した辺の終点で評価した、全延長から終点 fiber への同じ族。 -/
def fixedExtensionEdgeTarget : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S ≫ fixedExtensionEdgePrism p β i v hv k)
    (fixedExtensionEdgePrism_one_base p β i v hv k e hk)

/-- 始点評価は、同じ全延長の辺 prism の始点制限そのもの。 -/
lemma fixedExtensionEdgeSource_ι :
    fixedExtensionEdgeSource p β i v hv k e hk ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 S ≫ fixedExtensionEdgePrism p β i v hv k := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 終点評価も、同じ全延長の辺 prism の終点制限そのもの。 -/
lemma fixedExtensionEdgeTarget_ι :
    fixedExtensionEdgeTarget p β i v hv k e hk ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S ≫ fixedExtensionEdgePrism p β i v hv k := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 全延長の始点評価は、元の指定図式 W の同じ辺の始点を回収する。 -/
lemma fixedExtensionEdgeSource_vertex_val (W : K ⟶ E) (hW : W ≫ p = β) (hWi : i ≫ W = v) :
    ((fixedExtensionEdgeSource p β i v hv k e hk).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W, hW, hWi⟩)).val =
        W.app _ (k.app _ (stdSimplex.obj₀Equiv.symm 0)) := by
  rfl

/-- 全延長の終点評価も、元の指定図式 W の同じ辺の終点を回収する。 -/
lemma fixedExtensionEdgeTarget_vertex_val (W : K ⟶ E) (hW : W ≫ p = β) (hWi : i ≫ W = v) :
    ((fixedExtensionEdgeTarget p β i v hv k e hk).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W, hW, hWi⟩)).val =
        W.app _ (k.app _ (stdSimplex.obj₀Equiv.symm 1)) := by
  rfl

variable [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]

/-- 全延長の終点評価と、始点評価を指定辺で輸送した族の比較同型。 -/
def fixedExtensionEdgeTransportIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (fixedExtensionEdgeTarget p β i v hv k e hk)
    (fixedExtensionEdgeSource p β i v hv k e hk ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso p e _ _ (fixedExtensionEdgePrism p β i v hv k)
    (fixedExtensionEdgeSource_ι p β i v hv k e hk).symm
    (fixedExtensionEdgeTarget_ι p β i v hv k e hk).symm
    (fixedExtensionEdgePrism_projection p β i v hv k e hk)

/-- 延長空間の実際の辺の終点の像は、同じ輸送比較の二成分との自然性を満たす。 -/
lemma fixedExtensionEdgeTransportIso_naturality {x y : (S) _⦋0⦌} (s : (S).Edge x y) :
    (hoFunctor.map (fixedExtensionEdgeTarget p β i v hv k e hk)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk s.toTruncated) ≫
      (fixedExtensionEdgeTransportIso p β i v hv k e hk).toNatIso.hom.app
        (SSet.HomotopyCategory.mk y) =
      (fixedExtensionEdgeTransportIso p β i v hv k e hk).toNatIso.hom.app
          (SSet.HomotopyCategory.mk x) ≫
        (hoFunctor.map
          (fixedExtensionEdgeSource p β i v hv k e hk ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk s.toTruncated) :=
  (fixedExtensionEdgeTransportIso p β i v hv k e hk).toNatIso.hom.naturality _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
