module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSubsetQuotient
public import Mathlib.Algebra.CharP.Lemmas

/-! # 先行根関係のp乗商における後続根関係の正則性

標数pでは先行関係のp乗は指数p²のモニック根関係である。
既存の任意部分集合商の多項式表示を再利用する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 標数pの先行根関係のp乗イデアルは、指数p²の既存根関係イデアル。 -/
theorem deltaRootSubset_powerRelationIdeal_eq (hp : (p : A) = 0) (T : Set σ) (b : σ → A) :
    Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p) =
      deltaRootSubsetRelationIdeal (p := p * p) T (fun s ↦ b s ^ p) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := hA
    exact Subsingleton.elim _ _
  · have := hA
    have : CharP A p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    unfold deltaRootSubsetRelationIdeal
    congr 1
    congr 1
    funext t
    simp only [deltaRootRelationFamily, sub_pow_char, ← pow_mul, ← map_pow]

/-- 先行根関係のp乗で割った後も、残りの根関係は正則。先行集合の有限性は不要。 -/
theorem deltaRootSubsetPowerQuotient_remaining_isSMulRegular
    (hp : (p : A) = 0) (T : Set σ) (b : σ → A) (s : σ) (hs : s ∉ T) :
    IsSMulRegular
      (MvPolynomial σ A ⧸ Ideal.span
        (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p))
      (Ideal.Quotient.mk
        (Ideal.span (Set.range fun t : T ↦ (deltaRootRelationFamily (p := p) b t) ^ p))
        (deltaRootRelationFamily (p := p) b s)) := by
  rw [deltaRootSubset_powerRelationIdeal_eq hp]
  let e := deltaRootSubsetQuotientEquiv (p := p * p) T (fun t ↦ b t ^ p)
  let C := MonicPowerFamilyCover (p * p) T A (fun t ↦ b t ^ p)
  have he : e (Ideal.Quotient.mk _ (deltaRootRelationFamily (p := p) b s)) =
      deltaRootRelationFamily (p := p)
        (fun t : (Tᶜ : Set σ) ↦ algebraMap A C (b t)) ⟨s, hs⟩ := by
    simp only [deltaRootRelationFamily, map_sub, map_pow, e,
      deltaRootSubsetQuotientEquiv_C]
    rw [deltaRootSubsetQuotientEquiv_X_notMem T (fun t ↦ b t ^ p) ⟨s, hs⟩]
  have hr := deltaRootRelation_isSMulRegular (p := p)
    (fun t : (Tᶜ : Set σ) ↦ algebraMap A C (b t)) (⟨s, hs⟩ : (Tᶜ : Set σ))
  intro x y hxy
  apply e.injective
  apply hr
  have h := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using h

end SerrePositivity.BhattScholze
