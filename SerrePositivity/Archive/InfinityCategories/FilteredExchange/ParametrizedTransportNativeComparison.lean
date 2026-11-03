module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ParametrizedTransportComparisonFactory

/-!
概要：元の直接普遍比較を、元の定義内の同じ標的レコードへの指定比較へ戻す。
方針：元のレコード表示を変えず、全作用の端点表示変更だけを除去する。
規約：指定比較を保持。使われ方：公開した実標的証拠への比較の展開を分割する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全区間への直接比較は、元の定義内の同じ実標的との全作用比較と同じ値。 -/
lemma fiberTransportFamily_parametrized_heq_native {E B L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ) :
    let k := intervalMappingCurryOfEndpoints γ h₀ h₁
    let U₀ := (parametrizedFiberTransportFamily p a b).precomp k
    let he : (Δ[1] ◁ k) ≫ intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) = γ := by
      rw [← intervalMappingUncurry_precomp, Category.comp_id]
      exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁
    let U : FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ :=
      ⟨U₀.endpoint, U₀.prism, U₀.start, U₀.finish, by rw [U₀.over_base, he]⟩
    HEq (FiberTransportFamily.mapIso_parametrized p γ h₀ h₁ T)
      (FiberTransportFamily.mapIso p (𝟙 _) γ h₁ T U) := by
  have he : (Δ[1] ◁ intervalMappingCurryOfEndpoints γ h₀ h₁) ≫
      intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) = γ := by
    rw [← intervalMappingUncurry_precomp, Category.comp_id]
    exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁
  exact (heq_of_eq (fiberTransportFamily_parametrized_eq_from_family p γ h₀ h₁ T)).trans
    (transportComparisonFromUniversalFamily_heq_raw p γ h₁ T
      (parametrizedFiberTransportFamily p a b) (intervalMappingCurryOfEndpoints γ h₀ h₁) he)

end SerrePositivity.InfinityCategories.F2
