module

public import SerrePositivity.InfinityCategories.F2.TriangleFirstEdgePrismSquares
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionFiberWitnessRestriction

/-!
概要：最初の辺を全て固定した同じ全三角形の持ち上げを、実 fiber 終点で比較する。
方針：最初の辺の left anodyne 性による可縮な全延長空間の指定比較を使う。
規約：底・最初辺・全係数・二終点を保持。使われ方：長辺比較と最後辺比較の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (β : (Δ[2] : SSet.{u}) ⊗ A ⟶ B) (v : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
  (hv : v ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ β)
local notation "i" => stdSimplex.δ (2 : Fin 3) ▷ A
local notation "j" => prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)

/-- 最初辺全体を固定する全三角形の選択空間は、全係数・全高次を含めて可縮。 -/
lemma triangleFirstEdgeExtensionSpace_contractible :
    IsContractibleKan (relativeFunctorExtensionSpace p β i v hv) :=
  relativeFunctorExtensionSpace_isContractibleKan p β i
    (triangleFirstEdge_prism_leftAnodyne A) v hv

/-- 元の最初辺を全て共有する二つの全三角形の、同じ実 fiber 終点間の指定比較。 -/
def triangleFirstEdgeFiberComparison (z : B _⦋0⦌) (hj : j ≫ β = SSet.const z)
    (W₀ W₁ : (Δ[2] : SSet.{u}) ⊗ A ⟶ E) (h₀ : W₀ ≫ p = β) (h₁ : W₁ ≫ p = β)
    (hi₀ : i ≫ W₀ = v) (hi₁ : i ≫ W₁ = v)
    (g₀ g₁ : A ⟶ vertexFiber p z)
    (hj₀ : j ≫ W₀ = g₀ ≫ vertexFiberι p z) (hj₁ : j ≫ W₁ = g₁ ≫ vertexFiberι p z) :
    FunctorIso g₀ g₁ :=
  relativeExtensionFiberEndpoint_witnessIso p β i (triangleFirstEdge_prism_leftAnodyne A)
    v hv j z hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁

end SerrePositivity.InfinityCategories.F2
