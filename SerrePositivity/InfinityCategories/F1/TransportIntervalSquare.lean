module

public import SerrePositivity.InfinityCategories.F1.DiagonalFiberTransportSourceIso
public import SerrePositivity.InfinityCategories.F1.FunctorNaturalityTriangles

/-!
概要：同じパラメーター上の四つの辺と、その全体を保つ区間の四角形。
方針：各辺を両端固定の区間空間で指定し、四角形の四面と厳密に同定する。
規約：四頂点が互いに異なるとは仮定しない。
使われ方：右 Hom 合成の四角形の二通りの pointed 輸送の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ全パラメーター上の四辺を厳密に保つ、指定した四頂点の区間四角形。 -/
structure TransportIntervalSquare {B : SSet.{u}} (P : SSet.{u}) (a b c d : B _⦋0⦌) where
  /-- 最初の内側の辺。 -/
  bottom : P ⟶ intervalMappingSpace a b
  /-- 最後の内側の辺。 -/
  top : P ⟶ intervalMappingSpace c d
  /-- 最初の外側の辺。 -/
  left : P ⟶ intervalMappingSpace a c
  /-- 最後の外側の辺。 -/
  right : P ⟶ intervalMappingSpace b d
  /-- 四辺を同時に含む元の族。 -/
  square : Δ[1] ⊗ (Δ[1] ⊗ P) ⟶ B
  /-- 外側の零端は bottom。 -/
  zero : prismEndpoint 0 _ ≫ square = intervalMappingUncurry bottom
  /-- 外側の一端は top。 -/
  one : prismEndpoint 1 _ ≫ square = intervalMappingUncurry top
  /-- 内側の零端は left。 -/
  inner_zero : (Δ[1] ◁ prismEndpoint 0 _) ≫ square = intervalMappingUncurry left
  /-- 内側の一端は right。 -/
  inner_one : (Δ[1] ◁ prismEndpoint 1 _) ≫ square = intervalMappingUncurry right

/-- 指定した区間空間の射を厳密に被覆する prism の終点を、同じ対角輸送と比較する。 -/
def leftFibrationPrism_transportIntervalIso {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (c : P ⟶ intervalMappingSpace a b) (W : Δ[1] ⊗ P ⟶ E)
    (W₀ : prismEndpoint 0 _ ≫ W = f ≫ vertexFiberι p a)
    (W₁ : prismEndpoint 1 _ ≫ W = g ≫ vertexFiberι p b)
    (Wp : W ≫ p = intervalMappingUncurry c) :
    FunctorIso g (diagonalFiberTransport p f c) := by
  have e := leftFibrationPrism_diagonalTransportIso p f g (intervalMappingUncurry c)
    (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) W W₀ W₁ Wp
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry c)
      (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) = c := by
    apply intervalMappingUncurry_injective _ _
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  rw [hc] at e
  exact e

end SerrePositivity.InfinityCategories
