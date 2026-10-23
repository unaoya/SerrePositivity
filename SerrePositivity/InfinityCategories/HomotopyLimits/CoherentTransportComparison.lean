module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransportTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeExtensionHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConstantBaseEndpointHomotopy
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplexPrismFirstVertex

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (σ : SSet.Edge.CompStruct e f g)

/-- 元の三角形の長辺 prism と標準 prism の比較円柱と、底・始点の固定条件。 -/
structure CoherentTransportComparison where
  homotopy : SSet.Homotopy (coherentTransportTriangleLongPrism p σ) (transportEdgePrism p g)
  projection : homotopy.h ≫ p =
    fst ((Δ[1] : SSet.{u}) ⊗ vertexFiber p a) Δ[1] ≫
      fst (Δ[1] : SSet.{u}) (vertexFiber p a) ≫ SSet.yonedaEquiv.symm g.edge
  initial : ((scaffoldFirstVertex 1 ▷ vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    fst ((Δ[0] : SSet.{u}) ⊗ vertexFiber p a) Δ[1] ≫
      snd (Δ[0] : SSet.{u}) (vertexFiber p a) ≫ vertexFiberι p a

/-- 元の prism の双方と、その底・始点の固定条件を含む比較を選ぶ。 -/
def coherentTransportComparison : CoherentTransportComparison p σ :=
  Classical.choice (by
    let A := vertexFiber p a
    let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm g.edge
    let i := scaffoldFirstVertex 1 ▷ A
    let v := snd (Δ[0] : SSet.{u}) A ≫ vertexFiberι p a
    have h₀ : i ≫ coherentTransportTriangleLongPrism p σ = v := by
      dsimp only [i, v]
      rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] A ≫ prismEndpoint 0 A ≫ _ = _
      rw [coherentTransportTriangleLongPrism_zero]
    have h₀' : i ≫ transportEdgePrism p g = v := by
      dsimp only [i, v]
      rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
      change snd Δ[0] A ≫ prismEndpoint 0 A ≫ _ = _
      rw [transportEdgePrism_zero]
    have hv : v ≫ p = i ≫ β := by
      rw [← h₀, Category.assoc, coherentTransportTriangleLongPrism_projection]
    obtain ⟨H, hH, hI⟩ := exists_homotopy_over_fixed_extension p β i
      (simplexPrismFirstVertex_leftAnodyne 1 A) v hv
      (coherentTransportTriangleLongPrism p σ) (transportEdgePrism p g)
      (coherentTransportTriangleLongPrism_projection p σ)
      (transportEdgePrism_projection p g) h₀ h₀'
    exact ⟨⟨H, by simpa only [Category.assoc] using hH,
      by simpa only [Category.assoc] using hI⟩⟩)

/-- 同じ比較円柱を終点で評価した、二段階輸送から標準長辺輸送への実際のホモトピー。 -/
def coherentTransportTriangleCompositionHomotopy :
    SSet.Homotopy (edgeTransport p e ≫ edgeTransport p f) (edgeTransport p g) := by
  let A := vertexFiber p a
  let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm g.edge
  have hj : prismEndpoint 1 A ≫ β = SSet.const c := by
    dsimp only [β, A]
    rw [← coherentTransportTriangleLongPrism_projection p σ, ← Category.assoc,
      coherentTransportTriangleLongPrism_one, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  apply constantBaseEndpointHomotopy p β (coherentTransportComparison p σ).homotopy
    (by simpa only [Category.assoc] using (coherentTransportComparison p σ).projection)
    (prismEndpoint 1 A) c hj
    (edgeTransport p e ≫ edgeTransport p f) (edgeTransport p g)
    (coherentTransportTriangleLongPrism_one p σ) (transportEdgePrism_one p g)

/-- 終点比較の円柱は、元の相対比較を終点で制限した円柱へ厳密に射影する。 -/
lemma coherentTransportTriangleCompositionHomotopy_projection :
    (coherentTransportTriangleCompositionHomotopy p σ).h ≫ vertexFiberι p c =
      (prismEndpoint 1 (vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentTransportComparison p σ).homotopy.h := by
  dsimp only [coherentTransportTriangleCompositionHomotopy]
  rw [constantBaseEndpointHomotopy_projection]

/-- 実際の比較ホモトピーから作る合成同型。元の二単体を忘れる存在命題からは選ばない。 -/
def coherentTransportTriangleCompositionIso :
    FunctorIso (edgeTransport p e ≫ edgeTransport p f) (edgeTransport p g) := by
  letI : KanComplex (vertexFiber p c) := vertexFiber_kanComplex_of_leftFibration p c
  exact functorIsoOfSimplicialHomotopy (coherentTransportTriangleCompositionHomotopy p σ)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
