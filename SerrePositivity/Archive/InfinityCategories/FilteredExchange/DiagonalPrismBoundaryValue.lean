module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：元の実 prism と両 fiber の頂点を保つ表示変更は、同じ値射への指定比較を保つ。
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

/-- 同じ実 prism・両 fiber 頂点と値射の一致は、指定対角比較の値への後合成も保つ。 -/
lemma diagonalTransportIso_postcomp_heq_of_boundary {E B K Z : SSet.{u}}
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
    (ha : a = a') (hb : b = b') (hH : H = H')
    (V : vertexFiber p b ⟶ Z) (V' : vertexFiber p b' ⟶ Z) (hV : HEq V V') :
    HEq ((leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H hs he hp).postcomp V)
      (FunctorIso.postcomp
        (leftFibrationPrism_diagonalTransportIso p f' g' γ' h₀' h₁' H' hs' he' hp') V') := by
  cases ha
  cases hb
  have hγ : γ = γ' := hp.symm.trans ((congrArg (fun k => k ≫ p) hH).trans hp')
  cases hγ
  have hf : f = f' := (cancel_mono (vertexFiberι p a)).mp
    (hs.symm.trans ((congrArg (fun k => prismEndpoint 0 K ≫ k) hH).trans hs'))
  subst f'
  have hg : g = g' := (cancel_mono (vertexFiberι p b)).mp
    (he.symm.trans ((congrArg (fun k => prismEndpoint 1 K ≫ k) hH).trans he'))
  subst g'
  have hv := eq_of_heq hV
  subst V'
  have h := leftFibrationPrism_diagonalTransportIso_heq_of_prism_eq p f g g γ h₀ h₁
    H H' hs hs' he he' hp hp' hH
  exact heq_of_eq (congrArg (fun k => FunctorIso.postcomp k V) (eq_of_heq h))

end SerrePositivity.InfinityCategories.F2
