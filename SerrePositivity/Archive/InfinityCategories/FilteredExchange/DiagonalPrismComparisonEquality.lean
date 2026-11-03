module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonWitness

/-!
概要：同じ初期値・区間の実 prism の一致は、元の対角比較の指定値も一致させる。
方針：fiber 包含の単射性で実終点を回収し、元の実データの等式を消去する。
規約：比較を再選択しない。使われ方：元の全実長辺と native 比較の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ初期値・区間の実 prism の一致だけで、元の指定対角比較は両端も含めて一致。 -/
lemma leftFibrationPrism_diagonalTransportIso_heq_of_prism_eq {E B K : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : K ⟶ vertexFiber p a) (g g' : K ⟶ vertexFiber p b)
    (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (h₀ : prismEndpoint 0 K ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 K ≫ γ = SSet.const b)
    (H H' : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (hs : prismEndpoint 0 K ≫ H = f ≫ vertexFiberι p a)
    (hs' : prismEndpoint 0 K ≫ H' = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 K ≫ H = g ≫ vertexFiberι p b)
    (he' : prismEndpoint 1 K ≫ H' = g' ≫ vertexFiberι p b)
    (hp : H ≫ p = γ) (hp' : H' ≫ p = γ) (hH : H = H') :
    HEq (leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ H hs he hp)
      (leftFibrationPrism_diagonalTransportIso p f g' γ h₀ h₁ H' hs' he' hp') := by
  subst H'
  have hg : g = g' := (cancel_mono (vertexFiberι p b)).mp (he.symm.trans he')
  subst g'
  rfl

end SerrePositivity.InfinityCategories.F2
