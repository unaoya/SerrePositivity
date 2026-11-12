module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeExtensionEndpointClasses
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTransportTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeExtensionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftFibrationPrismTransport

/-!
概要：既存の prism 輸送比較同型を、同じ底と始点を保つ実際の円柱として実現する。
方針：元の prism と同じ標準 prism を相対的に比較し、その終点の辺の類を照合する。
規約：元の prism・底の辺・標準輸送を保持する。使われ方：指定境界経路の相対的な照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b : B _⦋0⦌} (e : B.Edge a b) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)
  (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
  (hH₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a)
  (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)

/-- 元の初期族によって同じ標準輸送 prism を引き戻したもの。 -/
def prismTransportStandard : (Δ[1] : SSet.{u}) ⊗ A ⟶ E :=
  (Δ[1] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p e

/-- 標準 prism の底は元の指定辺。 -/
lemma prismTransportStandard_projection :
    prismTransportStandard p e f ≫ p =
      fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [prismTransportStandard, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_projection,
    ← Category.assoc, whiskerLeft_fst]

/-- 標準 prism の初期値は指定した元の族。 -/
lemma prismTransportStandard_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ prismTransportStandard p e f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
  rw [prismTransportStandard, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero]

/-- 標準 prism の終点は元の輸送関手の適用そのもの。 -/
lemma prismTransportStandard_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ prismTransportStandard p e f =
      (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  rw [prismTransportStandard, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_one, Category.assoc]

/-- 元の prism と標準輸送の間の、底と初期値を同時に固定した比較円柱。 -/
structure PrismTransportCylinder where
  homotopy : SSet.Homotopy H (prismTransportStandard p e f)
  projection : homotopy.h ≫ p = fst ((Δ[1] : SSet.{u}) ⊗ A) Δ[1] ≫
    fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge
  initial : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    fst ((Δ[0] : SSet.{u}) ⊗ A) Δ[1] ≫ snd (Δ[0] : SSet.{u}) A ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a

/-- 指定した元の prism から、同じ底と初期値を保つ比較データを構成する。 -/
def prismTransportCylinder : PrismTransportCylinder p e f H :=
  Classical.choice (by
    let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge
    let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A
    let v := snd (Δ[0] : SSet.{u}) A ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a
    have hHi : i ≫ H = v := by
      dsimp only [i, v]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = _
      rw [hH₀]
    have hWi : i ≫ prismTransportStandard p e f = v := by
      dsimp only [i, v]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ prismTransportStandard p e f = _
      rw [prismTransportStandard_zero]
    have hv : v ≫ p = i ≫ β := by rw [← hHi, Category.assoc, hHp]
    obtain ⟨K, hK, hI⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_homotopy_over_fixed_extension p β i
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne 1 A) v hv H (prismTransportStandard p e f)
      hHp (prismTransportStandard_projection p e f) hHi hWi
    exact ⟨⟨K, by simpa only [Category.assoc] using hK,
      by simpa only [Category.assoc] using hI⟩⟩)

variable (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (hH₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)

/-- 同じ実際の相対円柱を終点で評価した、元の族から標準輸送への比較。 -/
def prismTransportEndpointHomotopy : SSet.Homotopy g (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy p
    (fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge)
    (prismTransportCylinder p e f H hH₀ hHp).homotopy
    (by simpa only [Category.assoc] using (prismTransportCylinder p e f H hH₀ hHp).projection)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) b
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : A ⟶ B)) e.tgt_eq))
    g (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) hH₁ (prismTransportStandard_one p e f)

/-- 終点比較の円柱は、底と初期値を保つ同じ円柱をそのまま制限したもの。 -/
lemma prismTransportEndpointHomotopy_projection :
    (prismTransportEndpointHomotopy p e f H hH₀ hHp g hH₁).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫
        (prismTransportCylinder p e f H hH₀ hHp).homotopy.h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantBaseEndpointHomotopy_projection _ _ _ _ _ _ _ _ _ _ _

/-- この実際の円柱の終点の類は、既存の prism 輸送比較同型の射そのもの。 -/
lemma prismTransportEndpointHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (prismTransportEndpointHomotopy p e f H hH₀ hHp g hH₁)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso p e f g H hH₀ hH₁ hHp).hom := by
  let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A
  let v := snd (Δ[0] : SSet.{u}) A ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a
  have hHi : i ≫ H = v := by
    dsimp only [i, v]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
    change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = _
    rw [hH₀]
  have hWi : i ≫ prismTransportStandard p e f = v := by
    dsimp only [i, v]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
    change snd Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ prismTransportStandard p e f = _
    rw [prismTransportStandard_zero]
  have hv : v ≫ p = i ≫ β := by rw [← hHi, Category.assoc, hHp]
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ β = SSet.const b :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : A ⟶ B)) e.tgt_eq)
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEndpointHomotopy_hom p β i (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne 1 A)
    v hv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) b hj H (prismTransportStandard p e f)
    hHp (prismTransportStandard_projection p e f) hHi hWi
    g (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) hH₁ (prismTransportStandard_one p e f)
    (prismTransportCylinder p e f H hH₀ hHp).homotopy
    (by simpa only [Category.assoc] using (prismTransportCylinder p e f H hH₀ hHp).projection)
    (by simpa only [Category.assoc] using (prismTransportCylinder p e f H hH₀ hHp).initial)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
