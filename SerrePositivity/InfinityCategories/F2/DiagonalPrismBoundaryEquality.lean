module

public import SerrePositivity.InfinityCategories.F2.DiagonalPrismComparisonEquality

/-!
概要：元の実 prism と両 fiber の頂点を保つ表示変更は、指定対角比較の値を保持する。
方針：同じ実 prism の射影で底、初点の fiber 包含の単射性で初期値を回収する。
規約：底・係数の整合を別途仮定しない。使われ方：raw/native の長辺比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実 prism と両 fiber 頂点の等式から、底・全初期値・終点・指定比較の一致を回収。 -/
lemma diagonalTransportIso_heq_of_boundary {E B K : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b a' b' : B _⦋0⦌}
    (f : K ⟶ vertexFiber p a) (f' : K ⟶ vertexFiber p a')
    (g : K ⟶ vertexFiber p b) (g' : K ⟶ vertexFiber p b')
    (γ γ' : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (h₀ : prismEndpoint 0 K ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 K ≫ γ = SSet.const b)
    (h₀' : prismEndpoint 0 K ≫ γ' = SSet.const a')
    (h₁' : prismEndpoint 1 K ≫ γ' = SSet.const b')
    (H H' : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (hs : prismEndpoint 0 K ≫ H = f ≫ vertexFiberι p a)
    (hs' : prismEndpoint 0 K ≫ H' = f' ≫ vertexFiberι p a')
    (he : prismEndpoint 1 K ≫ H = g ≫ vertexFiberι p b)
    (he' : prismEndpoint 1 K ≫ H' = g' ≫ vertexFiberι p b')
    (hp : H ≫ p = γ) (hp' : H' ≫ p = γ')
    (ha : a = a') (hb : b = b') (hH : H = H') :
    HEq (leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H hs he hp)
      (leftFibrationPrism_diagonalTransportIso p f' g' γ' h₀' h₁' H' hs' he' hp') := by
  cases ha
  cases hb
  have hγ : γ = γ' := hp.symm.trans ((congrArg (fun k => k ≫ p) hH).trans hp')
  cases hγ
  have hf : f = f' := (cancel_mono (vertexFiberι p a)).mp
    (hs.symm.trans ((congrArg (fun k => prismEndpoint 0 K ≫ k) hH).trans hs'))
  subst f'
  exact leftFibrationPrism_diagonalTransportIso_heq_of_prism_eq p f g g' γ h₀ h₁
    H H' hs hs' he he' hp hp' hH

end SerrePositivity.InfinityCategories.F2
