module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalPrismBoundaryValue
/-!
概要：同じ実 prism の native 輸送の値射を実境界から照合する。
方針：射影から同じ底、初点の fiber 包含から同じ初期値を回収する。
規約：指定比較の HEq から端点を抽出しない。
使われ方：零面側と元の Apex 側の native 値の実端点照合。
-/

@[expose] public section
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
/-- 概要：同じ実 prism と両 fiber 頂点・値射は同じ native 値射を与える。
方針：実底と初期値を射影と包含で照合する。
規約：同じ元の輸送と値射を保持。使われ方：二辺値の実中間終点。 -/
lemma diagonalFiberTransport_value_eq_of_prism_boundary {E B K Z : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b a' b' : B _⦋0⦌}
    (f : K ⟶ vertexFiber p a) (f' : K ⟶ vertexFiber p a')
    (γ γ' : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (h₀ : prismEndpoint 0 K ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 K ≫ γ = SSet.const b)
    (h₀' : prismEndpoint 0 K ≫ γ' = SSet.const a')
    (h₁' : prismEndpoint 1 K ≫ γ' = SSet.const b')
    (H H' : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (hs : prismEndpoint 0 K ≫ H = f ≫ vertexFiberι p a)
    (hs' : prismEndpoint 0 K ≫ H' = f' ≫ vertexFiberι p a')
    (hp : H ≫ p = γ) (hp' : H' ≫ p = γ')
    (ha : a = a') (hb : b = b') (hH : H = H')
    (V : vertexFiber p b ⟶ Z) (V' : vertexFiber p b' ⟶ Z) (hV : HEq V V') :
    diagonalFiberTransport p f (intervalMappingCurryOfEndpoints γ h₀ h₁) ≫ V =
      diagonalFiberTransport p f' (intervalMappingCurryOfEndpoints γ' h₀' h₁') ≫ V' := by
  cases ha
  cases hb
  have hγ : γ = γ' := hp.symm.trans ((congrArg (fun k => k ≫ p) hH).trans hp')
  cases hγ
  have hf : f = f' := (cancel_mono (vertexFiberι p a)).mp
    (hs.symm.trans ((congrArg (fun k => prismEndpoint 0 K ≫ k) hH).trans hs'))
  subst f'
  cases eq_of_heq hV
  rfl
end
end SerrePositivity.InfinityCategories.F2
