module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionUniversalPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation

/-!
概要：全 prism の普遍評価の終点を、同じ指定 fiber 内の全終点写像として保持する。
方針：元の全延長の fiber 終点評価を uncurry し、実 prism の終点を回収する。
規約：全選択・実終点・元の値を保持。使われ方：最後辺の普遍輸送を全最初辺へ適用する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K E B : SSet.{u}} (p : E ⟶ B) (β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
  (v : K ⟶ E) (hv : v ≫ p = prismEndpoint 0 K ≫ β)
  (z : B _⦋0⦌) (hz : prismEndpoint 1 K ≫ β = SSet.const z)
local notation "Q" => relativeFunctorExtensionSpace p β (prismEndpoint 0 K) v hv

/-- 元の全 prism の実終点を、同じ指定 fiber への一つの全射として保持する。 -/
def relativeExtensionUniversalPrismEndpoint : K ⊗ Q ⟶ vertexFiber p z :=
  uncurry (relativeExtensionFiberEndpoint p β (prismEndpoint 0 K) v hv
    (prismEndpoint 1 K) z hz)

/-- 同じ全普遍 prism の実終点は、同じ元の全 fiber 評価の包含そのもの。 -/
lemma relativeExtensionUniversalPrism_finish :
    prismEndpoint 1 (K ⊗ Q) ≫ relativeExtensionUniversalPrism p β v hv =
      relativeExtensionUniversalPrismEndpoint p β v hv z hz ≫ vertexFiberι p z := by
  rw [relativeExtensionUniversalPrism, ← Category.assoc, prismEndpoint_associator_inv,
    relativeExtensionUniversalPrismEndpoint, relativeExtensionFiberEndpoint_uncurry_ι,
    relativeFunctorUncurry_pre]

end SerrePositivity.InfinityCategories.F2
