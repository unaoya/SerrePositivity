module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # 相対自由変数の任意有限初期段と後続段の分離

初期N段を係数多項式へ、残りを外側多項式へ送る標準同型。
N=0と任意添字を含み、δ構造の保存や平坦性はこの同型だけから主張しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable (N : ℕ) (σ : Type u) (A : Type v) [CommRing A]

/-- 初期N段と残りを分け、後続段の番号をNだけ繰り下げる添字同値。 -/
def relativeFreeFiniteVariableSplit : σ × ℕ ≃ (σ × ℕ) ⊕ (σ × Fin N) where
  toFun z := if h : z.2 < N then Sum.inr (z.1, ⟨z.2, h⟩) else Sum.inl (z.1, z.2 - N)
  invFun z := match z with
    | Sum.inl (s, n) => (s, n + N)
    | Sum.inr (s, i) => (s, i.val)
  left_inv z := by
    obtain ⟨s, n⟩ := z
    by_cases hn : n < N
    · simp [hn]
    · simp [hn, Nat.sub_add_cancel (by omega : N ≤ n)]
  right_inv z := by
    cases z with
    | inl z =>
        obtain ⟨s, n⟩ := z
        simp [show ¬n + N < N by omega]
    | inr z =>
        obtain ⟨s, i⟩ := z
        simp [i.isLt]

/-- 初期N段の添字は係数側へ送られる。 -/
@[simp] theorem relativeFreeFiniteVariableSplit_initial (s : σ) (i : Fin N) :
    relativeFreeFiniteVariableSplit N σ (s, i.val) = Sum.inr (s, i) := by
  simp [relativeFreeFiniteVariableSplit, i.isLt]

/-- 後続段の添字は外側へ送られる。 -/
@[simp] theorem relativeFreeFiniteVariableSplit_tail (s : σ) (n : ℕ) :
    relativeFreeFiniteVariableSplit N σ (s, n + N) = Sum.inl (s, n) := by
  simp [relativeFreeFiniteVariableSplit, show ¬n + N < N by omega]

/-- 相対自由環を、初期N段の係数多項式環上の後続多項式環へ分離する。 -/
def relativeFreeFiniteVariableSplitAlgEquiv :
    RelativeFreeDeltaRing (R := A) σ ≃ₐ[A]
      MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin N) A) :=
  (MvPolynomial.renameEquiv A (relativeFreeFiniteVariableSplit N σ)).trans
    (MvPolynomial.sumAlgEquiv A (σ × ℕ) (σ × Fin N))

/-- 分離同型は元の係数を二重の係数射へ送る。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_C (a : A) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [relativeFreeFiniteVariableSplitAlgEquiv]

/-- 初期N段の変数は係数多項式の変数となる。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_X_initial (s : σ) (i : Fin N) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (MvPolynomial.X (s, i.val)) =
      MvPolynomial.C (MvPolynomial.X (s, i)) := by
  simp [relativeFreeFiniteVariableSplitAlgEquiv]

/-- 後続変数は外側の変数となる。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_X_tail (s : σ) (n : ℕ) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (MvPolynomial.X (s, n + N)) =
      MvPolynomial.X (s, n) := by
  simp [relativeFreeFiniteVariableSplitAlgEquiv]

/-- 有限初期段の変数を元の相対自由環へ含める標準射。 -/
def relativeFreeFiniteInitialPolynomialMap :
    MvPolynomial (σ × Fin N) A →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.rename (fun z => (z.1, z.2.val))

/-- 後続変数を元の相対自由環へ含める標準射。 -/
def relativeFreeFiniteTailPolynomialMap :
    MvPolynomial (σ × ℕ) A →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.rename (fun z => (z.1, z.2 + N))

/-- 任意の有限初期多項式の包含は、分離後の係数射となる。 -/
theorem relativeFreeFiniteVariableSplitAlgEquiv_initial (f : MvPolynomial (σ × Fin N) A) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (relativeFreeFiniteInitialPolynomialMap N σ A f) =
      MvPolynomial.C f := by
  have he : (relativeFreeFiniteVariableSplitAlgEquiv N σ A).toRingHom.comp
      (relativeFreeFiniteInitialPolynomialMap N σ A).toRingHom =
      (MvPolynomial.C : MvPolynomial (σ × Fin N) A →+*
        MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin N) A)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeFiniteInitialPolynomialMap]
    · intro z
      obtain ⟨s, i⟩ := z
      simp [relativeFreeFiniteInitialPolynomialMap]
  exact RingHom.congr_fun he f

/-- 任意の後続多項式の包含は、分離後の係数包含による写像となる。 -/
theorem relativeFreeFiniteVariableSplitAlgEquiv_tail (f : MvPolynomial (σ × ℕ) A) :
    relativeFreeFiniteVariableSplitAlgEquiv N σ A (relativeFreeFiniteTailPolynomialMap N σ A f) =
      MvPolynomial.map (MvPolynomial.C : A →+* MvPolynomial (σ × Fin N) A) f := by
  have he : (relativeFreeFiniteVariableSplitAlgEquiv N σ A).toRingHom.comp
      (relativeFreeFiniteTailPolynomialMap N σ A).toRingHom =
      MvPolynomial.map (MvPolynomial.C : A →+* MvPolynomial (σ × Fin N) A) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeFiniteTailPolynomialMap]
    · intro z
      obtain ⟨s, n⟩ := z
      simp [relativeFreeFiniteTailPolynomialMap]
  exact RingHom.congr_fun he f

/-- 逆同型は二重の係数を元の係数へ戻す。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_symm_C_C (a : A) :
    (relativeFreeFiniteVariableSplitAlgEquiv N σ A).symm (MvPolynomial.C (MvPolynomial.C a)) =
      MvPolynomial.C a := by
  apply (relativeFreeFiniteVariableSplitAlgEquiv N σ A).injective
  simp

/-- 逆同型は係数側変数を初期段の変数へ戻す。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_symm_C_X (s : σ) (i : Fin N) :
    (relativeFreeFiniteVariableSplitAlgEquiv N σ A).symm (MvPolynomial.C (MvPolynomial.X (s, i))) =
      MvPolynomial.X (s, i.val) := by
  apply (relativeFreeFiniteVariableSplitAlgEquiv N σ A).injective
  simp

/-- 逆同型は外側変数をN以降の変数へ戻す。 -/
@[simp] theorem relativeFreeFiniteVariableSplitAlgEquiv_symm_X (s : σ) (n : ℕ) :
    (relativeFreeFiniteVariableSplitAlgEquiv N σ A).symm (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n + N) := by
  apply (relativeFreeFiniteVariableSplitAlgEquiv N σ A).injective
  simp

end SerrePositivity.BhattScholze
