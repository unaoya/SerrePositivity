module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismBoundaryValue
/-!
概要：同じ実 prism の対角値を元の左因子に続けた比のまま表示変更する。
方針：同じ prism の射影から底を回収し、同じ指定対角値へ帰着する。
規約：実両端・左因子・値射を固定する。
使われ方：raw 最後辺の比を一般区間族の比へ戻す。
-/

@[expose] public section
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
/-- 概要：同じ実 prism の値の表示変更は元の左因子を保つ。
方針：同じ底へ移し、同じ指定対角比較を後合成する。
規約：左因子を再選択しない。使われ方：raw 比の区間表示。 -/
lemma diagonalTransportIso_left_postcomp_heq_of_prism {E B K Z : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : K ⟶ vertexFiber p a) (g : K ⟶ vertexFiber p b)
    (γ γ' : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (h₀ : prismEndpoint 0 K ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 K ≫ γ = SSet.const b)
    (h₀' : prismEndpoint 0 K ≫ γ' = SSet.const a)
    (h₁' : prismEndpoint 1 K ≫ γ' = SSet.const b)
    (H H' : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (hs : prismEndpoint 0 K ≫ H = f ≫ vertexFiberι p a)
    (hs' : prismEndpoint 0 K ≫ H' = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 K ≫ H = g ≫ vertexFiberι p b)
    (he' : prismEndpoint 1 K ≫ H' = g ≫ vertexFiberι p b)
    (hp : H ≫ p = γ) (hp' : H' ≫ p = γ') (hH : H = H')
    (V : vertexFiber p b ⟶ Z) {t : K ⟶ Z} (L : FunctorIso t (g ≫ V)) :
    HEq (L ≪≫ (leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H hs he hp).postcomp V)
      (L ≪≫
        (leftFibrationPrism_diagonalTransportIso p f g γ' h₀' h₁' H' hs' he' hp').postcomp V) := by
  have hγ : γ = γ' := hp.symm.trans ((congrArg (fun k => k ≫ p) hH).trans hp')
  cases hγ
  have h := leftFibrationPrism_diagonalTransportIso_heq_of_prism_eq p f g g γ h₀ h₁
    H H' hs hs' he he' hp hp' hH
  exact heq_of_eq (congrArg (fun e => L ≪≫ FunctorIso.postcomp e V) (eq_of_heq h))
end
end SerrePositivity.InfinityCategories.F2
