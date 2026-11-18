module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalBoundaryValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalBoundaryValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MixedBoundaryValues

/-!
模型。文献の定義との比較は後で
# BF境界の全添字の符号付き対合

Berger–Fresse §2.2.7、M14 L09a。
固定点の零と三方向の実境界値の比較を、構成済みの同じ対合へ渡す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- C255：既存の対合の両側の実境界値は、元の加群で負号により一致する。 -/
lemma boundaryBalancePerm_neg (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex w q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm w q i) x =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q i x := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner_neg_of_cases (r + d) q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_fixed_zero A S w q x)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_horizontal_neg A S w q x)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_vertical_neg A S w q x)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_mixed_neg A S w q x)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv w q) i)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_partner, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue_at_index] using ht

/-- L09a：固定点の零も保持した、全BF境界項の同じ符号付き対合。 -/
theorem boundaryBalance_pairing {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) :
    ∃ τ : Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex w q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q (τ i) x = -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q i x) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm w q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_involutive w q, ?_, ?_⟩
  · intro i hi A _ S x
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_fixed_zero A S w q i hi x
  · intro i _ A _ S x
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_neg A S w q x i

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
