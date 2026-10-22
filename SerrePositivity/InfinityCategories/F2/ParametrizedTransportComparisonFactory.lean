module

public import SerrePositivity.InfinityCategories.F2.TransportComparisonFromUniversalFamily

/-!
概要：元の F1 の直接普遍比較は、元の同じ普遍輸送族を一般表示へ入力した値である。
方針：元の二証拠・同じ区間制限・同じ表示変更を、そのまま厳密に照合する。
規約：元の比較を保持。使われ方：直接比較の値照合を具体的輸送族から分離する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の直接普遍比較は、同じ元の普遍輸送族を用いた一般の表示そのもの。 -/
lemma fiberTransportFamily_parametrized_eq_from_family {E B L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ) :
    FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T =
      transportComparisonFromUniversalFamily p γ h₁ T (parametrizedFiberTransportFamily p a b)
        (intervalMappingCurryOfEndpoints γ h₀ h₁)
        (by
          rw [← intervalMappingUncurry_precomp, Category.comp_id]
          exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁) := rfl

end SerrePositivity.InfinityCategories.F2
