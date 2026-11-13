module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentTransportTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.RelativeExtensionHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.ConstantBaseEndpointHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：元の三角形 prism の長辺と標準長辺輸送を、底と初期値を固定する実際の円柱で比較する。
方針：同じ相対延長の空間で比較を選び、終点で評価した fiber 内のホモトピーから同型を作る。
規約：二辺の輸送関手の間の任意の同型を選ばず、元の prism に射影する比較データを保持する。
使われ方：元の native な二単体に依存する境界の輸送経路。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (σ : SSet.Edge.CompStruct e f g)

/-- 元の三角形の長辺 prism と標準 prism の比較円柱と、底・始点の固定条件。 -/
structure CoherentTransportComparison where
  homotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism p σ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p g)
  projection : homotopy.h ≫ p =
    fst ((Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) Δ[1] ≫
      fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ SSet.yonedaEquiv.symm g.edge
  initial : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    fst ((Δ[0] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) Δ[1] ≫
      snd (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a

/-- 元の prism の双方と、その底・始点の固定条件を含む比較を選ぶ。 -/
def coherentTransportComparison : CoherentTransportComparison p σ :=
  Classical.choice (by
    let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a
    let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm g.edge
    let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A
    let v := snd (Δ[0] : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a
    have h₀ : i ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism p σ = v := by
      dsimp only [i, v]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_zero]
    have h₀' : i ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p g = v := by
      dsimp only [i, v]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero]
    have hv : v ≫ p = i ≫ β := by
      rw [← h₀, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_projection]
    obtain ⟨H, hH, hI⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_homotopy_over_fixed_extension p β i
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne 1 A) v hv
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism p σ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p g)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_projection p σ)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection p g) h₀ h₀'
    exact ⟨⟨H, by simpa only [Category.assoc] using hH,
      by simpa only [Category.assoc] using hI⟩⟩)

/-- 同じ比較円柱を終点で評価した、二段階輸送から標準長辺輸送への実際のホモトピー。 -/
def coherentTransportTriangleCompositionHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p g) := by
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a
  let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm g.edge
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ β = SSet.const c := by
    dsimp only [β, A]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_projection p σ, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_one, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy p β (coherentTransportComparison p σ).homotopy
    (by simpa only [Category.assoc] using (coherentTransportComparison p σ).projection)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) c hj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p g)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleLongPrism_one p σ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_one p g)

/-- 終点比較の円柱は、元の相対比較を終点で制限した円柱へ厳密に射影する。 -/
lemma coherentTransportTriangleCompositionHomotopy_projection :
    (coherentTransportTriangleCompositionHomotopy p σ).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentTransportComparison p σ).homotopy.h := by
  dsimp only [coherentTransportTriangleCompositionHomotopy]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy_projection]

/-- 実際の比較ホモトピーから作る合成同型。元の二単体を忘れる存在命題からは選ばない。 -/
def coherentTransportTriangleCompositionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p g) := by
  letI : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p c
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (coherentTransportTriangleCompositionHomotopy p σ)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
