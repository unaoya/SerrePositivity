module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Composition

/-!
概要：元の二単体と二つの輸送 prism を保持する、輸送の合成の実際の三角形データ。
方針：二辺の prism を貼り、底の二単体を厳密に指定して三角形 prism を延長する。
規約：存在命題だけの輸送証人へ戻してから選び直さず、選んだ同じ prism を使う。
使われ方：native な span の二単体への依存を保つ境界経路と、その高次の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 標準輸送で選んだ実際の辺 prism。二単体の合成でも同じ二辺を使う。 -/
def transportEdgePrism {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : B _⦋0⦌} (e : B.Edge a b) : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p e).choose

/-- 標準辺 prism の始点は元の fiber の包含。 -/
lemma transportEdgePrism_zero {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : B _⦋0⦌} (e : B.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ transportEdgePrism p e = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p e).choose_spec.1

/-- 標準辺 prism の終点は元の標準輸送。 -/
lemma transportEdgePrism_one {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : B _⦋0⦌} (e : B.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ transportEdgePrism p e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p e).choose_spec.2.1

/-- 標準辺 prism の底は元の辺そのもの。 -/
lemma transportEdgePrism_projection {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {a b : B _⦋0⦌} (e : B.Edge a b) :
    transportEdgePrism p e ≫ p =
      fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ SSet.yonedaEquiv.symm e.edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p e).choose_spec.2.2.1

variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (σ : SSet.Edge.CompStruct e f g)

/-- 二辺の標準 prism と底の二単体を厳密に保持する三角形 prism のデータ。 -/
structure CoherentTransportTriangle where
  prism : (Δ[2] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ E
  first : (stdSimplex.δ (2 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ prism = transportEdgePrism p e
  second : (stdSimplex.δ (0 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ prism =
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) ≫ transportEdgePrism p f
  projection : prism ≫ p =
    fst (Δ[2] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ SSet.yonedaEquiv.symm σ.simplex

/-- 元の二辺と元の二単体の双方を含む条件を満たす三角形 prism を選ぶ。 -/
def coherentTransportTriangle : CoherentTransportTriangle p σ :=
  Classical.choice (by
    let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a
    let H' := (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e) ≫ transportEdgePrism p f
    let β := fst (Δ[2] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm σ.simplex
    have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ transportEdgePrism p e = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H' := by
      dsimp only [H']
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
        transportEdgePrism_zero, transportEdgePrism_one]
    have h₀₁ : transportEdgePrism p e ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ β := by
      rw [transportEdgePrism_projection]
      change fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge =
        (fst (Δ[1] : SSet.{u}) A ≫ stdSimplex.δ (2 : Fin 3)) ≫
          SSet.yonedaEquiv.symm σ.simplex
      rw [Category.assoc, σ.δ_two_yonedaEquiv_symm]
    have h₁₂ : H' ≫ p = (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ β := by
      dsimp only [H']
      rw [Category.assoc, transportEdgePrism_projection]
      change fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm f.edge =
        (fst (Δ[1] : SSet.{u}) A ≫ stdSimplex.δ (0 : Fin 3)) ≫
          SSet.yonedaEquiv.symm σ.simplex
      rw [Category.assoc, σ.δ_zero_yonedaEquiv_symm]
    obtain ⟨T, hT₀₁, hT₁₂, hTp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.innerFibration_fillTrianglePrism p
      (transportEdgePrism p e) H' β hw h₀₁ h₁₂
    exact ⟨⟨T, hT₀₁, hT₁₂, hTp⟩⟩)

/-- 選んだ同じ三角形 prism の長辺。 -/
def coherentTransportTriangleLongPrism : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ E :=
  (stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ (coherentTransportTriangle p σ).prism

/-- 長辺 prism の始点は元の fiber の包含。 -/
lemma coherentTransportTriangleLongPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ coherentTransportTriangleLongPrism p σ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫
      (stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ (stdSimplex.δ (2 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) := rfl
  rw [coherentTransportTriangleLongPrism, ← Category.assoc, hz, Category.assoc,
    (coherentTransportTriangle p σ).first, transportEdgePrism_zero]

/-- 長辺 prism の終点は元の二辺の標準輸送の合成。 -/
lemma coherentTransportTriangleLongPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ coherentTransportTriangleLongPrism p σ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c := by
  have ho : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫
      (stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ (stdSimplex.δ (0 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) := rfl
  rw [coherentTransportTriangleLongPrism, ← Category.assoc, ho, Category.assoc,
    (coherentTransportTriangle p σ).second, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, transportEdgePrism_one, Category.assoc]

/-- 長辺 prism の底は元の長辺。元の二単体との関係も三角形データに保持する。 -/
lemma coherentTransportTriangleLongPrism_projection :
    coherentTransportTriangleLongPrism p σ ≫ p =
      fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ SSet.yonedaEquiv.symm g.edge := by
  rw [coherentTransportTriangleLongPrism, Category.assoc,
    (coherentTransportTriangle p σ).projection]
  change (fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) ≫ stdSimplex.δ (1 : Fin 3)) ≫
      SSet.yonedaEquiv.symm σ.simplex = _
  rw [Category.assoc, σ.δ_one_yonedaEquiv_symm]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
