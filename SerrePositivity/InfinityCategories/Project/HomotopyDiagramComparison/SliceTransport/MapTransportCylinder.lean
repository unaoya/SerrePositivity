module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PrismTransportCylinder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTransportNaturality

/-!
概要：底上の射に関する標準輸送の自然性を、底・初期値固定の実際の円柱として保持する。
方針：同じ二つの標準 prism を比較し、終点の類を既存の自然性同型と照合する。
規約：元の prism と射を保持する。使われ方：指定境界経路の制限自然性の部分の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
  (f : E ⟶ E') (hf : f ≫ q = p) {a b : B _⦋0⦌} (e : B.Edge a b)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a
local notation "F₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf a
local notation "F₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b

/-- 始域の同じ標準 prism に底上の射を後合成したもの。 -/
def mapTransportPrism : (Δ[1] : SSet.{u}) ⊗ A ⟶ E' := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p e ≫ f

include hf in
omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] in
/-- 後合成した prism も、元の指定辺を厳密に被覆する。 -/
lemma mapTransportPrism_projection :
    mapTransportPrism p f e ≫ q =
      fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [mapTransportPrism, Category.assoc, hf, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection]

omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] in
/-- 後合成した prism の初期値は、同じ fiber 射と包含の合成。 -/
lemma mapTransportPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ mapTransportPrism p f e = F₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q a := by
  rw [mapTransportPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]

omit [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] in
/-- 後合成した prism の終点は、元の輸送後に終点 fiber の射を施したもの。 -/
lemma mapTransportPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ mapTransportPrism p f e =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b := by
  rw [mapTransportPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_one]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]

/-- 同じ二つの標準 prism を比較する、底・初期値固定の実際の円柱データ。 -/
def mapTransportCylinderData :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportCylinder q e F₀ (mapTransportPrism p f e)
    (mapTransportPrism_zero p q f hf e) (mapTransportPrism_projection p q f hf e)

/-- 自然性の正方形を結ぶ、同じ相対円柱の終点での実際の比較。 -/
def mapTransportEndpointHomotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁)
    (F₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q e) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportEndpointHomotopy q e F₀ (mapTransportPrism p f e)
    (mapTransportPrism_zero p q f hf e) (mapTransportPrism_projection p q f hf e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁) (mapTransportPrism_one p q f hf e)

/-- 自然性の円柱は、底・初期値固定の同じ円柱の終点制限へ射影する。 -/
lemma mapTransportEndpointHomotopy_projection :
    (mapTransportEndpointHomotopy p q f hf e).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫
        (mapTransportCylinderData p q f hf e).homotopy.h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportEndpointHomotopy_projection _ _ _ _ _ _ _ _

/-- 終点比較の類は、既存の標準輸送の自然性同型の射そのもの。 -/
lemma mapTransportEndpointHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (mapTransportEndpointHomotopy p q f hf e)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso p q f hf e).hom := by
  let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A
  let v := snd (Δ[0] : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a ≫ f
  let W := mapTransportPrism p f e
  let W' := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard q e F₀
  have hWi : i ≫ W = v := by
    dsimp only [i, v, W, mapTransportPrism]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
    change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p e ≫ f) = _
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A), _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero]
  have hWi' : i ≫ W' = v := by
    dsimp only [i, v, W']
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
    change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard q e F₀ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  have hv : v ≫ q = i ≫ β := by
    rw [← hWi, Category.assoc, mapTransportPrism_projection p q f hf e]
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ β = SSet.const b :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : A ⟶ B)) e.tgt_eq)
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEndpointHomotopy_hom q β i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne 1 A) v hv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) b hj
    W W' (mapTransportPrism_projection p q f hf e)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_projection q e F₀) hWi hWi'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ F₁) (F₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q e)
    (mapTransportPrism_one p q f hf e) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard_one q e F₀)
    (mapTransportCylinderData p q f hf e).homotopy
    (by simpa only [Category.assoc] using (mapTransportCylinderData p q f hf e).projection)
  have h := (mapTransportCylinderData p q f hf e).initial
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι] using h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
