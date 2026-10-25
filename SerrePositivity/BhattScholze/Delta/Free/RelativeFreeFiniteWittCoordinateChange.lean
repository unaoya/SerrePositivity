module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWittInverseSupport

/-! # 通常有限多項式環上のWitt座標代数同型

初期変数部分代数との同型で制限済み座標同型を移す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期変数部分集合と有限段添字の標準同型。 -/
def relativeFreeFiniteSupportedIndexEquiv (N : ℕ) (σ : Type v) :
    {z : σ × ℕ // z.2 < N} ≃ σ × Fin N where
  toFun z := (z.val.1, ⟨z.val.2, z.property⟩)
  invFun z := ⟨(z.1, z.2.val), z.2.isLt⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

/-- 初期N段の有限多項式環と、全変数環の初期部分代数の標準同型。 -/
def relativeFreeFiniteSupportedEquiv (N : ℕ) (σ : Type v) (A : Type u) [CommRing A] :
    MvPolynomial (σ × Fin N) A ≃ₐ[A] MvPolynomial.supported A {z : σ × ℕ | z.2 < N} :=
  (MvPolynomial.renameEquiv A (relativeFreeFiniteSupportedIndexEquiv N σ).symm).trans
    (MvPolynomial.supportedEquivMvPolynomial {z : σ × ℕ | z.2 < N}).symm

/-- 初期部分代数同型の係数包含は既存の標準初期多項式射そのもの。 -/
theorem relativeFreeFiniteSupportedEquiv_coe (N : ℕ) (f : MvPolynomial (σ × Fin N) A) :
    (relativeFreeFiniteSupportedEquiv N σ A f : RelativeFreeDeltaRing (R := A) σ) =
      relativeFreeFiniteInitialPolynomialMap N σ A f := by
  have he : (MvPolynomial.supported A {z : σ × ℕ | z.2 < N}).val.comp
      (relativeFreeFiniteSupportedEquiv N σ A).toAlgHom =
        relativeFreeFiniteInitialPolynomialMap N σ A := by
    apply MvPolynomial.algHom_ext
    intro z
    change ((MvPolynomial.supportedEquivMvPolynomial (R := A) {z : σ × ℕ | z.2 < N}).symm
      (MvPolynomial.rename (relativeFreeFiniteSupportedIndexEquiv N σ).symm
        (MvPolynomial.X z))).val = _
    rw [MvPolynomial.rename_X, MvPolynomial.supportedEquivMvPolynomial_symm_X]
    simp only [relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_X]
    rfl
  exact AlgHom.congr_fun he f

/-- 初期N段の通常多項式環上の実際のWitt座標代数同型。 -/
def relativeFreeFiniteWittCoordinateEquiv (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ) :
    MvPolynomial (σ × Fin N) A ≃ₐ[A] MvPolynomial (σ × Fin N) A :=
  (relativeFreeFiniteSupportedEquiv N σ A).trans
    ((relativeFreeWittSupportedEquiv D hp N).trans (relativeFreeFiniteSupportedEquiv N σ A).symm)

/-- 有限座標同型と全座標射の標準包含図式。 -/
theorem relativeFreeFiniteWittCoordinateEquiv_initial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : MvPolynomial (σ × Fin N) A) :
    relativeFreeFiniteInitialPolynomialMap N σ A (relativeFreeFiniteWittCoordinateEquiv D hp N f) =
      relativeFreeWittCoordinateMap D (relativeFreeFiniteInitialPolynomialMap N σ A f) := by
  let F := relativeFreeFiniteSupportedEquiv N σ A
  let E := relativeFreeWittSupportedEquiv (σ := σ) D hp N
  calc
    _ = (F (relativeFreeFiniteWittCoordinateEquiv D hp N f) : RelativeFreeDeltaRing (R := A) σ) :=
      (relativeFreeFiniteSupportedEquiv_coe N _).symm
    _ = (E (F f) : RelativeFreeDeltaRing (R := A) σ) := by
      change (F (F.symm (E (F f))) : RelativeFreeDeltaRing (R := A) σ) = _
      rw [F.apply_symm_apply]
    _ = relativeFreeWittCoordinateMap D (F f : RelativeFreeDeltaRing (R := A) σ) :=
      relativeFreeWittSupportedEquiv_coe D hp N (F f)
    _ = _ := by rw [relativeFreeFiniteSupportedEquiv_coe]

/-- 有限逆座標同型の標準包含図式。 -/
theorem relativeFreeFiniteWittCoordinateEquiv_symm_initial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ)
    (f : MvPolynomial (σ × Fin N) A) :
    relativeFreeFiniteInitialPolynomialMap N σ A
      ((relativeFreeFiniteWittCoordinateEquiv D hp N).symm f) =
        relativeFreeWittInverseMap D hp (relativeFreeFiniteInitialPolynomialMap N σ A f) := by
  let E := relativeFreeFiniteWittCoordinateEquiv (σ := σ) D hp N
  have he := relativeFreeFiniteWittCoordinateEquiv_initial D hp N (E.symm f)
  rw [E.apply_symm_apply] at he
  have hc := AlgHom.congr_fun (relativeFreeWittInverseMap_comp_coordinateMap D hp)
    (relativeFreeFiniteInitialPolynomialMap N σ A (E.symm f))
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at hc
  exact hc.symm.trans (congrArg (relativeFreeWittInverseMap D hp) he.symm)

/-- 有限座標同型は各有限δ変数を対応する全Witt係数へ移す。 -/
theorem relativeFreeFiniteWittCoordinateEquiv_X_initial (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (N : ℕ) (s : σ) (i : Fin N) :
    relativeFreeFiniteInitialPolynomialMap N σ A
      (relativeFreeFiniteWittCoordinateEquiv D hp N (MvPolynomial.X (s, i))) =
        relativeFreeWittGhostCoefficient D s i.val := by
  rw [relativeFreeFiniteWittCoordinateEquiv_initial]
  have hx : relativeFreeFiniteInitialPolynomialMap N σ A (MvPolynomial.X (s, i)) =
      MvPolynomial.X (s, i.val) := by simp [relativeFreeFiniteInitialPolynomialMap]
  rw [hx, relativeFreeWittCoordinateMap, MvPolynomial.aeval_X]

end SerrePositivity.BhattScholze
