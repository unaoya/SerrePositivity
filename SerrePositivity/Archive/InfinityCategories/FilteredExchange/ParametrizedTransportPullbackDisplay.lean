module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ParametrizedTransportPullbackFamily

/-!
概要：公開した普遍輸送の制限証拠を、元の F1 の直接比較内の標的レコードへ同定する。
方針：元の全区間制限・実終点・実 prism をそのまま表示する。
規約：全実データを保持。使われ方：巨大な指定比較の型の正規化を分割する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 公開した元の制限証拠は、元の F1 の直接比較に用いた同じ標的レコード。 -/
lemma parametrizedTransportPullbackFamily_eq_native {E B L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₀ : prismEndpoint 0 L ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b) :
    parametrizedTransportPullbackFamily p γ h₀ h₁ =
      (let k := intervalMappingCurryOfEndpoints γ h₀ h₁
       let U₀ := (parametrizedFiberTransportFamily p a b).precomp k
       let he : (Δ[1] ◁ k) ≫ intervalMappingUncurry (𝟙 (intervalMappingSpace a b)) = γ := by
         rw [← intervalMappingUncurry_precomp, Category.comp_id]
         exact intervalMappingUncurry_curryOfEndpoints γ h₀ h₁
       (⟨U₀.endpoint, U₀.prism, U₀.start, U₀.finish, by rw [U₀.over_base, he]⟩ :
         FiberTransportFamily (b := b) p (𝟙 (vertexFiber p a)) γ)) := rfl

end SerrePositivity.InfinityCategories.F2
