module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTransportTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeTrianglePrismHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：同じ native な二単体と標準二辺を持つ輸送三角形の選択を、境界を固定して比較する。
方針：内ホーン上で定値な相対円柱を選び、同じ円柱を長辺へ制限する。
規約：円柱の底・二辺・長辺の端点条件を一緒に保持する。
使われ方：輸送三角形の選択を替えても、全 Hom の境界比較を整合させるための入力。
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
  (T T' : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTransportTriangle p σ)

/-- 三角形全体の比較と、底・標準二辺を固定する円柱の式。 -/
structure CoherentTransportTriangleHomotopy where
  homotopy : SSet.Homotopy T.prism T'.prism
  projection : homotopy.h ≫ p =
    fst ((Δ[2] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) Δ[1] ≫
      fst (Δ[2] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ SSet.yonedaEquiv.symm σ.simplex
  first : ((stdSimplex.δ (2 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
    homotopy.h = fst ((Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p e
  second : ((stdSimplex.δ (0 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
    homotopy.h = fst ((Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) Δ[1] ≫
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism p f

/-- 同じ底と標準二辺を持つ実際の輸送三角形を、二辺を保つ円柱で比較する。 -/
def coherentTransportTriangleHomotopy : CoherentTransportTriangleHomotopy p σ T T' :=
  Classical.choice (by
    obtain ⟨H, hbase, hfirst, hsecond⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_trianglePrism_homotopy_relative_spine p
      (fst (Δ[2] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ SSet.yonedaEquiv.symm σ.simplex)
      T.prism T'.prism T.projection T'.projection
      (T.first.trans T'.first.symm) (T.second.trans T'.second.symm)
    exact ⟨⟨H, by simpa only [Category.assoc] using hbase,
      by simpa only [← Category.assoc, T'.first] using hfirst,
      by simpa only [← Category.assoc, T'.second, Category.assoc] using hsecond⟩⟩)

/-- 同じ比較円柱を長辺へ制限する。 -/
def coherentTransportTriangleLongHomotopy :
    SSet.Homotopy ((stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ T.prism)
      ((stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ T'.prism) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (coherentTransportTriangleHomotopy p σ T T').homotopy
    (stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)

/-- 長辺の円柱の底は、元の長辺上で時間方向に定値。 -/
lemma coherentTransportTriangleLongHomotopy_projection :
    (coherentTransportTriangleLongHomotopy p σ T T').h ≫ p =
      fst ((Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) Δ[1] ≫
        fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ SSet.yonedaEquiv.symm g.edge := by
  dsimp only [coherentTransportTriangleLongHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp]
  rw [Category.assoc, (coherentTransportTriangleHomotopy p σ T T').projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc]
  change _ ≫ (fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫
    stdSimplex.δ (1 : Fin 3)) ≫ SSet.yonedaEquiv.symm σ.simplex = _
  rw [Category.assoc, σ.δ_one_yonedaEquiv_symm]

/-- 長辺の始点は、元の始点 fiber の包含上で時間方向に定値。 -/
lemma coherentTransportTriangleLongHomotopy_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentTransportTriangleLongHomotopy p σ T T').h =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) := rfl
  dsimp only [coherentTransportTriangleLongHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp]
  rw [← Category.assoc, ← comp_whiskerRight, hz, comp_whiskerRight, Category.assoc,
    (coherentTransportTriangleHomotopy p σ T T').first, ← Category.assoc,
    whiskerRight_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_zero]

/-- 長辺の終点は、二段階輸送の同じ関手上で時間方向に定値。 -/
lemma coherentTransportTriangleLongHomotopy_one :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentTransportTriangleLongHomotopy p σ T T').h =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) Δ[1] ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c := by
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) := rfl
  dsimp only [coherentTransportTriangleLongHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp]
  rw [← Category.assoc, ← comp_whiskerRight, ho, comp_whiskerRight, Category.assoc,
    (coherentTransportTriangleHomotopy p σ T T').second, ← Category.assoc,
    whiskerRight_fst, Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism_one, Category.assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
