module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryCancellationReduction

/-!
模型。文献の定義との比較は後で
# 実際のBF境界値の添字の移送

Berger–Fresse §2.2.7、M14 L09aの証明分割。
同じ境界値を、語に依らない有限添字で読む。複体や界面の型は変更しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 既存の境界値を同じ添字の同値に沿って読む。 -/
def universalBoundaryValue (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex (r + d) q →
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1) :=
  fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv w q).symm i) x

lemma universalBoundaryValue_at_index (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex w q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv w q) i) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q i x := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue
  rw [Equiv.symm_apply_apply]

lemma universalBoundaryValue_partner (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex w q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner (r + d) q ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv w q) i)) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm w q i) x := rfl

lemma universalBoundaryValue_fixed_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex (r + d) q) (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner (r + d) q i = i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryValue A S w q x i = 0 := by
  have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm w q ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv w q).symm i) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv w q).symm i :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_fixed_iff w q _).mpr (by
      simpa only [Equiv.apply_symm_apply] using hi)
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_fixed_zero A S w q _ hf x

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
