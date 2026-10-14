module

public import SerrePositivity.BhattScholze.RelativeFreeFiniteDeltaStep
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # 有限次段の最高変数と初期変数の分離

最高段を外側変数、初期段を係数多項式へ送る標準同型。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable (N : ℕ) (σ : Type u) (A : Type v) [CommRing A]

/-- 次の有限段の最高変数を左項へ分ける添字同値。 -/
def relativeFreeFiniteTopVariableSplit : σ × Fin (N + 2) ≃ σ ⊕ (σ × Fin (N + 1)) where
  toFun z := if h : z.2.val < N + 1 then Sum.inr (z.1, ⟨z.2.val, h⟩) else Sum.inl z.1
  invFun z := match z with
    | Sum.inl s => (s, Fin.last (N + 1))
    | Sum.inr (s, i) => (s, i.castSucc)
  left_inv z := by
    obtain ⟨s, i⟩ := z
    by_cases hi : i.val < N + 1
    · simp [hi]
    · simp only [dite_eq_right hi, Prod.mk.injEq, true_and]
      apply Fin.ext
      have hn := i.isLt
      simp only [Fin.val_last]
      omega
  right_inv z := by
    cases z with
    | inl s => simp
    | inr z =>
        obtain ⟨s, i⟩ := z
        simp [i.isLt]

/-- 最高変数の添字は外側へ送られる。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplit_top (s : σ) :
    relativeFreeFiniteTopVariableSplit N σ (s, Fin.last (N + 1)) = Sum.inl s := by
  simp [relativeFreeFiniteTopVariableSplit]

/-- 初期変数の添字は係数側へ送られる。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplit_initial (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteTopVariableSplit N σ (s, i.castSucc) = Sum.inr (s, i) := by
  have hi : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  simp [relativeFreeFiniteTopVariableSplit, hi]

/-- 有限次段は、初期有限変数の係数多項式環上の最高変数の多項式環。 -/
def relativeFreeFiniteTopVariableSplitAlgEquiv :
    MvPolynomial (σ × Fin (N + 2)) A ≃ₐ[A]
      MvPolynomial σ (MvPolynomial (σ × Fin (N + 1)) A) :=
  (MvPolynomial.renameEquiv A (relativeFreeFiniteTopVariableSplit N σ)).trans
    (MvPolynomial.sumAlgEquiv A σ (σ × Fin (N + 1)))

/-- 最高変数分離の係数上の式。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplitAlgEquiv_C (a : A) :
    relativeFreeFiniteTopVariableSplitAlgEquiv N σ A (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [relativeFreeFiniteTopVariableSplitAlgEquiv]

/-- 最高変数分離の最高変数上の式。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplitAlgEquiv_X_top (s : σ) :
    relativeFreeFiniteTopVariableSplitAlgEquiv N σ A (MvPolynomial.X (s, Fin.last (N + 1))) =
      MvPolynomial.X s := by
  simp [relativeFreeFiniteTopVariableSplitAlgEquiv]

/-- 最高変数分離の初期変数上の式。 -/
@[simp] theorem relativeFreeFiniteTopVariableSplitAlgEquiv_X_initial (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteTopVariableSplitAlgEquiv N σ A (MvPolynomial.X (s, i.castSucc)) =
      MvPolynomial.C (MvPolynomial.X (s, i)) := by
  simp [relativeFreeFiniteTopVariableSplitAlgEquiv]

/-- 次段への標準包含は、最高変数分離後の係数射となる。 -/
theorem relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteTopVariableSplitAlgEquiv N σ A (relativeFreeFiniteStepInclusion N σ f) =
      MvPolynomial.C f := by
  have he : (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom.comp
      (relativeFreeFiniteStepInclusion N σ) =
      (MvPolynomial.C : MvPolynomial (σ × Fin (N + 1)) A →+*
        MvPolynomial σ (MvPolynomial (σ × Fin (N + 1)) A)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeFiniteStepInclusion]
    · intro z
      obtain ⟨s, i⟩ := z
      simp [relativeFreeFiniteStepInclusion]
  exact RingHom.congr_fun he f

end SerrePositivity.BhattScholze
