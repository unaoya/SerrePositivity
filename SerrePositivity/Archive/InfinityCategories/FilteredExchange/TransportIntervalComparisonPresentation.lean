module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalSquare
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismBoundaryEquality

/-!
概要：元の区間空間による指定比較を、同じ実区間の対角比較へ値まで戻す。
方針：curry・uncurry の往復による終点表示の移送だけを除く。
規約：元の指定比較を保持。使われ方：四角形の三辺の指定自然性の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の区間比較は、元の同じ実 prism の指定対角比較と値まで一致する。 -/
lemma leftFibrationPrism_transportIntervalIso_heq_diagonal {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (c : P ⟶ intervalMappingSpace a b) (W : Δ[1] ⊗ P ⟶ E)
    (W₀ : prismEndpoint 0 P ≫ W = f ≫ vertexFiberι p a)
    (W₁ : prismEndpoint 1 P ≫ W = g ≫ vertexFiberι p b)
    (Wp : W ≫ p = intervalMappingUncurry c) :
    HEq (leftFibrationPrism_transportIntervalIso p f g c W W₀ W₁ Wp)
      (leftFibrationPrism_diagonalTransportIso p f g (intervalMappingUncurry c)
        (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) W W₀ W₁ Wp) := by
  have hcast {α β : Sort (u + 1)} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  unfold leftFibrationPrism_transportIntervalIso
  exact hcast _ _

/-- 同じ実 prism の底の表示を揃えると、元の対角比較は元の区間比較へ値まで戻る。 -/
lemma leftFibrationPrism_diagonal_heq_interval_of_base {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (γ : Δ[1] ⊗ P ⟶ B)
    (h₀ : prismEndpoint 0 P ≫ γ = SSet.const a)
    (h₁ : prismEndpoint 1 P ≫ γ = SSet.const b)
    (W : Δ[1] ⊗ P ⟶ E)
    (W₀ : prismEndpoint 0 P ≫ W = f ≫ vertexFiberι p a)
    (W₁ : prismEndpoint 1 P ≫ W = g ≫ vertexFiberι p b) (Wp : W ≫ p = γ)
    (c : P ⟶ intervalMappingSpace a b) (hc : γ = intervalMappingUncurry c) :
    HEq (leftFibrationPrism_diagonalTransportIso p f g γ h₀ h₁ W W₀ W₁ Wp)
      (leftFibrationPrism_transportIntervalIso p f g c W W₀ W₁ (Wp.trans hc)) := by
  exact (diagonalTransportIso_heq_of_boundary p f f g g γ (intervalMappingUncurry c)
    h₀ h₁ (intervalMappingUncurry_zero c) (intervalMappingUncurry_one c) W W
    W₀ W₀ W₁ W₁ Wp (Wp.trans hc) rfl rfl rfl).trans
      (leftFibrationPrism_transportIntervalIso_heq_diagonal p f g c W W₀ W₁ (Wp.trans hc)).symm

end SerrePositivity.InfinityCategories.F2
