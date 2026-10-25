module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # 相対自由δ環の初期変数と後続変数の分離

台多項式環の同型。後続変数のδ段番号は一つ繰り下げる。
δ構造の保存や商・完備化の平坦性をこの同型だけからは主張しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable (σ : Type u) (A : Type v) [CommRing A]

/-- 初期段を右項へ、後続段を左項へ分ける添字同値。 -/
def relativeFreeVariableSplit : σ × ℕ ≃ (σ × ℕ) ⊕ σ where
  toFun z := match z.2 with
    | 0 => Sum.inr z.1
    | n + 1 => Sum.inl (z.1, n)
  invFun z := match z with
    | Sum.inl (s, n) => (s, n + 1)
    | Sum.inr s => (s, 0)
  left_inv z := by obtain ⟨s, n⟩ := z; cases n <;> rfl
  right_inv z := by cases z with
    | inl z => obtain ⟨s, n⟩ := z; rfl
    | inr s => rfl

/-- 初期段の添字は係数側の変数へ送られる。 -/
@[simp] theorem relativeFreeVariableSplit_zero (s : σ) :
    relativeFreeVariableSplit σ (s, 0) = Sum.inr s := rfl

/-- 後続段の添字は外側の変数へ送られる。 -/
@[simp] theorem relativeFreeVariableSplit_succ (s : σ) (n : ℕ) :
    relativeFreeVariableSplit σ (s, n + 1) = Sum.inl (s, n) := rfl

/-- 相対自由環は初期変数の多項式環上の、後続変数の多項式環。 -/
def relativeFreeVariableSplitAlgEquiv :
    RelativeFreeDeltaRing (R := A) σ ≃ₐ[A] MvPolynomial (σ × ℕ) (MvPolynomial σ A) :=
  (MvPolynomial.renameEquiv A (relativeFreeVariableSplit σ)).trans
    (MvPolynomial.sumAlgEquiv A (σ × ℕ) σ)

/-- 変数分離は元の係数を二重の係数射へ送る。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_C (a : A) :
    relativeFreeVariableSplitAlgEquiv σ A (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [relativeFreeVariableSplitAlgEquiv]

/-- 初期変数は係数多項式の変数となる。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_X_zero (s : σ) :
    relativeFreeVariableSplitAlgEquiv σ A (MvPolynomial.X (s, 0)) =
      MvPolynomial.C (MvPolynomial.X s) := by
  simp [relativeFreeVariableSplitAlgEquiv]

/-- 後続δ変数は外側の変数となる。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_X_succ (s : σ) (n : ℕ) :
    relativeFreeVariableSplitAlgEquiv σ A (MvPolynomial.X (s, n + 1)) =
      MvPolynomial.X (s, n) := by
  simp [relativeFreeVariableSplitAlgEquiv]

/-- 初期変数だけの多項式の標準包含。 -/
def relativeFreeInitialPolynomialMap : MvPolynomial σ A →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.rename (fun s => (s, 0))

/-- 後続変数だけの多項式の標準包含。 -/
def relativeFreeSuccessorPolynomialMap :
    MvPolynomial (σ × ℕ) A →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.rename (fun z => (z.1, z.2 + 1))

/-- 初期多項式の包含は変数分離で係数射となる。 -/
theorem relativeFreeVariableSplitAlgEquiv_initial (f : MvPolynomial σ A) :
    relativeFreeVariableSplitAlgEquiv σ A (relativeFreeInitialPolynomialMap σ A f) =
      MvPolynomial.C f := by
  have he : (relativeFreeVariableSplitAlgEquiv σ A).toRingHom.comp
      (relativeFreeInitialPolynomialMap σ A).toRingHom =
      (MvPolynomial.C : MvPolynomial σ A →+* MvPolynomial (σ × ℕ) (MvPolynomial σ A)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeInitialPolynomialMap]
    · intro s
      simp [relativeFreeInitialPolynomialMap]
  exact RingHom.congr_fun he f

/-- 後続多項式の包含は変数分離で係数の包含による写像となる。 -/
theorem relativeFreeVariableSplitAlgEquiv_successor (f : MvPolynomial (σ × ℕ) A) :
    relativeFreeVariableSplitAlgEquiv σ A (relativeFreeSuccessorPolynomialMap σ A f) =
      MvPolynomial.map (MvPolynomial.C : A →+* MvPolynomial σ A) f := by
  have he : (relativeFreeVariableSplitAlgEquiv σ A).toRingHom.comp
      (relativeFreeSuccessorPolynomialMap σ A).toRingHom =
      MvPolynomial.map (MvPolynomial.C : A →+* MvPolynomial σ A) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeSuccessorPolynomialMap]
    · intro z
      obtain ⟨s, n⟩ := z
      simp [relativeFreeSuccessorPolynomialMap]
  exact RingHom.congr_fun he f

/-- 分離同型の逆は二重係数を元の係数へ戻す。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_symm_C_C (a : A) :
    (relativeFreeVariableSplitAlgEquiv σ A).symm (MvPolynomial.C (MvPolynomial.C a)) =
      MvPolynomial.C a := by
  apply (relativeFreeVariableSplitAlgEquiv σ A).injective
  simp

/-- 分離同型の逆は係数側変数を初期変数へ戻す。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_symm_C_X (s : σ) :
    (relativeFreeVariableSplitAlgEquiv σ A).symm (MvPolynomial.C (MvPolynomial.X s)) =
      MvPolynomial.X (s, 0) := by
  apply (relativeFreeVariableSplitAlgEquiv σ A).injective
  simp

/-- 分離同型の逆は外側変数を後続δ変数へ戻す。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_symm_X (s : σ) (n : ℕ) :
    (relativeFreeVariableSplitAlgEquiv σ A).symm (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n + 1) := by
  apply (relativeFreeVariableSplitAlgEquiv σ A).injective
  simp

end SerrePositivity.BhattScholze
