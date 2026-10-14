module

public import SerrePositivity.BhattScholze.DeltaRootPartialQuotient
public import Mathlib.Logic.Equiv.Set

/-! # 任意の先行添字集合の根関係の商

有限性を要求せず、補集合の変数と先行指定根を具体的に分離する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A] {σ : Type v}

/-- 任意の先行添字集合Tについて、残りの添字を先に置く標準添字分割。 -/
def deltaRootSubsetIndexEquiv (T : Set σ) : σ ≃ (Tᶜ : Set σ) ⊕ T := by
  classical
  exact (Equiv.Set.sumCompl T).symm.trans (Equiv.sumComm _ _)

/-- 先行添字は分割の右側へ送られる。 -/
theorem deltaRootSubsetIndexEquiv_mem (T : Set σ) (s : T) :
    deltaRootSubsetIndexEquiv T s = Sum.inr s := by
  classical
  simp [deltaRootSubsetIndexEquiv]

/-- 残りの添字は分割の左側へ送られる。 -/
theorem deltaRootSubsetIndexEquiv_notMem (T : Set σ) (s : (Tᶜ : Set σ)) :
    deltaRootSubsetIndexEquiv T s = Sum.inl s := by
  classical
  simp [deltaRootSubsetIndexEquiv]

/-- 指定した部分集合の根関係のみを課すイデアル。 -/
def deltaRootSubsetRelationIdeal (T : Set σ) (b : σ → A) : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range fun s : T ↦ deltaRootRelationFamily (p := p) b s)

/-- 再添字付けで部分集合の関係式イデアルが先行変数の関係式イデアルへ移る。 -/
theorem deltaRootSubsetRelationIdeal_map_rename (T : Set σ) (b : σ → A) :
    (deltaRootSubsetRelationIdeal (p := p) T b).map
      (MvPolynomial.renameEquiv A (deltaRootSubsetIndexEquiv T)).toRingHom =
    deltaRootPartialRelationIdeal (p := p)
      (Sum.elim (fun t : (Tᶜ : Set σ) ↦ b t) (fun t : T ↦ b t)) := by
  simp only [deltaRootSubsetRelationIdeal, deltaRootPartialRelationIdeal,
    Ideal.map_span, ← Set.range_comp']
  congr 1
  congr 1
  funext s
  simp [deltaRootRelationFamily, MvPolynomial.renameEquiv,
    deltaRootSubsetIndexEquiv_mem]

/-- 任意部分集合の根関係の商は、既存根添加環上の補集合の多項式環。 -/
def deltaRootSubsetQuotientEquiv (T : Set σ) (b : σ → A) :
    (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) ≃+*
      MvPolynomial (Tᶜ : Set σ) (MonicPowerFamilyCover p T A (fun s ↦ b s)) :=
  (Ideal.quotientEquiv _ _ (MvPolynomial.renameEquiv A
    (deltaRootSubsetIndexEquiv T)).toRingEquiv
    (deltaRootSubsetRelationIdeal_map_rename T b).symm).trans
    (deltaRootPartialQuotientEquiv (p := p)
      (Sum.elim (fun t : (Tᶜ : Set σ) ↦ b t) (fun t : T ↦ b t)))

/-- 部分集合商の同型は元の係数を標準係数像へ送る。 -/
theorem deltaRootSubsetQuotientEquiv_C (T : Set σ) (b : σ → A) (a : A) :
    deltaRootSubsetQuotientEquiv (p := p) T b (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (algebraMap A (MonicPowerFamilyCover p T A (fun s ↦ b s)) a) := by
  change deltaRootPartialQuotientEquiv _ (Ideal.Quotient.mk _
    (MvPolynomial.renameEquiv A (deltaRootSubsetIndexEquiv T) (MvPolynomial.C a))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
  exact deltaRootPartialQuotientEquiv_C _ a

/-- 補集合の変数は、商表示の残りの多項式変数に一致する。 -/
theorem deltaRootSubsetQuotientEquiv_X_notMem (T : Set σ) (b : σ → A)
    (s : (Tᶜ : Set σ)) :
    deltaRootSubsetQuotientEquiv (p := p) T b (Ideal.Quotient.mk _ (MvPolynomial.X (s : σ))) =
      MvPolynomial.X s := by
  change deltaRootPartialQuotientEquiv _ (Ideal.Quotient.mk _
    (MvPolynomial.renameEquiv A (deltaRootSubsetIndexEquiv T) (MvPolynomial.X (s : σ)))) = _
  simp only [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    deltaRootSubsetIndexEquiv_notMem, deltaRootPartialQuotientEquiv_X_inl]

/-- 先行部分集合の変数は既存の指定根の係数像に一致する。 -/
theorem deltaRootSubsetQuotientEquiv_X_mem (T : Set σ) (b : σ → A) (s : T) :
    deltaRootSubsetQuotientEquiv (p := p) T b (Ideal.Quotient.mk _ (MvPolynomial.X (s : σ))) =
      MvPolynomial.C (monicPowerFamilyRoot p T A (fun t ↦ b t) s) := by
  change deltaRootPartialQuotientEquiv _ (Ideal.Quotient.mk _
    (MvPolynomial.renameEquiv A (deltaRootSubsetIndexEquiv T) (MvPolynomial.X (s : σ)))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, deltaRootSubsetIndexEquiv_mem]
  exact deltaRootPartialQuotientEquiv_X_inr _ s

/-- 先行部分集合に属さない根関係は、その商において非零因子。 -/
theorem deltaRootSubsetQuotient_remaining_isSMulRegular [Fact p.Prime]
    (T : Set σ) (b : σ → A) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b)
      (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := p) T b)
        (deltaRootRelationFamily (p := p) b s)) := by
  let e := deltaRootSubsetQuotientEquiv (p := p) T b
  have he : e (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := p) T b)
      (deltaRootRelationFamily (p := p) b s)) =
      deltaRootRelationFamily (p := p)
        (fun t : (Tᶜ : Set σ) ↦ algebraMap A (MonicPowerFamilyCover p T A
          (fun r ↦ b r)) (b t)) ⟨s, hs⟩ := by
    simp only [deltaRootRelationFamily, map_sub, map_pow, e,
      deltaRootSubsetQuotientEquiv_C]
    rw [deltaRootSubsetQuotientEquiv_X_notMem T b ⟨s, hs⟩]
  have h := deltaRootRelation_isSMulRegular (p := p)
    (fun t : (Tᶜ : Set σ) ↦ algebraMap A (MonicPowerFamilyCover p T A
      (fun r ↦ b r)) (b t)) (⟨s, hs⟩ : (Tᶜ : Set σ))
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

end SerrePositivity.BhattScholze
