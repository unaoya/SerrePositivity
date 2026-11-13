module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryCancellationReduction

/-!
# 実際のBF境界値の添字の移送

Berger–Fresse §2.2.7、M14 L09aの証明分割。
同じ境界値を、語に依らない有限添字で読む。複体や界面の型は変更しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial

/-- 既存の境界値を同じ添字の同値に沿って読む。 -/
def universalBoundaryValue (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    UniversalBoundaryIndex (r + d) q →
      (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1) :=
  fun i => boundaryBalanceTerm A S w q ((boundaryBalanceIndexEquiv w q).symm i) x

lemma universalBoundaryValue_at_index (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : BoundaryBalanceIndex w q) :
    universalBoundaryValue A S w q x ((boundaryBalanceIndexEquiv w q) i) =
      boundaryBalanceTerm A S w q i x := by
  unfold universalBoundaryValue
  rw [Equiv.symm_apply_apply]

lemma universalBoundaryValue_partner (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : BoundaryBalanceIndex w q) :
    universalBoundaryValue A S w q x
      (universalBoundaryPartner (r + d) q ((boundaryBalanceIndexEquiv w q) i)) =
        boundaryBalanceTerm A S w q (boundaryBalancePerm w q i) x := rfl

lemma universalBoundaryValue_fixed_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (i : UniversalBoundaryIndex (r + d) q) (hi : universalBoundaryPartner (r + d) q i = i) :
    universalBoundaryValue A S w q x i = 0 := by
  have hf : boundaryBalancePerm w q ((boundaryBalanceIndexEquiv w q).symm i) =
      (boundaryBalanceIndexEquiv w q).symm i :=
    (boundaryBalancePerm_fixed_iff w q _).mpr (by
      simpa only [Equiv.apply_symm_apply] using hi)
  exact boundaryBalancePerm_fixed_zero A S w q _ hf x

end SerrePositivity.EInfinity.SimplexCuts
