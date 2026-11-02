module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonWitness
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessIdentity
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportIntervalComparisonPresentation

/-!
概要：元の普遍 prism 自身の、元の区間表示による指定比較は恒等。
方針：同じ二実延長の fiber 終点比較へ戻し、curry の往復を消す。
規約：元の指定同型を保持。使われ方：任意の実面と固定底辺の比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の普遍 prism の対角比較は、curry の同じ表示変更を除けば恒等。 -/
lemma leftFibrationPrism_diagonalTransportIso_universal_heq_refl {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : P ⟶ vertexFiber p a)
    (γ : Δ[1] ⊗ P ⟶ B) (h₀ : prismEndpoint 0 P ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 P ≫ γ = SSet.const b)
    (c : P ⟶ intervalMappingSpace a b) (hc : intervalMappingCurryOfEndpoints γ h₀ h₁ = c)
    (hp : diagonalUniversalPrism p f c ≫ p = γ) :
    HEq (leftFibrationPrism_diagonalTransportIso p f (diagonalFiberTransport p f c) γ h₀ h₁
      (diagonalUniversalPrism p f c) (diagonalUniversalPrism_start p f c)
      (diagonalUniversalPrism_finish p f c) hp)
      (Iso.refl (HomotopyCategory.mk (functorVertex (diagonalFiberTransport p f c)))) := by
  subst c
  apply heq_of_eq
  rw [leftFibrationPrism_diagonalTransportIso_eq_witness]
  apply relativeExtensionFiberEndpoint_witnessIso_refl

/-- 元の普遍 prism に対する元の区間比較は、元の終点の恒等同型。 -/
lemma leftFibrationPrism_transportIntervalIso_universal_refl {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a b) :
    leftFibrationPrism_transportIntervalIso p f (diagonalFiberTransport p f c) c
      (diagonalUniversalPrism p f c) (diagonalUniversalPrism_start p f c)
      (diagonalUniversalPrism_finish p f c) (diagonalUniversalPrism_projection p f c) =
        Iso.refl _ := by
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry c)
      (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) = c := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  exact eq_of_heq ((leftFibrationPrism_transportIntervalIso_heq_diagonal p f
    (diagonalFiberTransport p f c) c (diagonalUniversalPrism p f c)
    (diagonalUniversalPrism_start p f c) (diagonalUniversalPrism_finish p f c)
    (diagonalUniversalPrism_projection p f c)).trans
      (leftFibrationPrism_diagonalTransportIso_universal_heq_refl p f
        (intervalMappingUncurry c) (intervalMappingUncurry_zero c)
        (intervalMappingUncurry_one c) c hc (diagonalUniversalPrism_projection p f c)))

/-- 同じ実区間の表示変更は、元の指定区間比較の値を保持する。 -/
lemma leftFibrationPrism_transportIntervalIso_eq_of_prism_eq {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (c : P ⟶ intervalMappingSpace a b) (W W' : Δ[1] ⊗ P ⟶ E)
    (hs : prismEndpoint 0 P ≫ W = f ≫ vertexFiberι p a)
    (hs' : prismEndpoint 0 P ≫ W' = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 P ≫ W = g ≫ vertexFiberι p b)
    (he' : prismEndpoint 1 P ≫ W' = g ≫ vertexFiberι p b)
    (hp : W ≫ p = intervalMappingUncurry c) (hp' : W' ≫ p = intervalMappingUncurry c)
    (h : W = W') :
    leftFibrationPrism_transportIntervalIso p f g c W hs he hp =
      leftFibrationPrism_transportIntervalIso p f g c W' hs' he' hp' := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.F2
