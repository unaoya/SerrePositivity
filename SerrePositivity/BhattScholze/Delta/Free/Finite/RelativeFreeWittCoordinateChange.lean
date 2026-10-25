module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeWittGhostTriangular

/-! # 全Witt座標とδ変数の三角形代数同型

下位有限多項式を評価して逆変数を強帰納で構成する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- δ変数を構成済みWitt係数へ送る相対多項式代数射。 -/
def relativeFreeWittCoordinateMap (D : DeltaStructure p A) :
    RelativeFreeDeltaRing (R := A) σ →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.aeval (fun z => relativeFreeWittGhostCoefficient D z.1 z.2)

/-- 第n逆変数は、初期n段の逆変数による下位多項式評価を引いて構成する。 -/
def relativeFreeWittInverseVariable (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    ℕ → σ → RelativeFreeDeltaRing (R := A) σ :=
  Nat.strongRec (fun n rec s => MvPolynomial.X (s, n) -
    MvPolynomial.aeval (fun z : σ × Fin n => rec z.2.val z.2.isLt z.1)
      (relativeFreeWittGhostLowerPolynomial D hp s n))

/-- 段数の強帰納による逆変数の評価式。 -/
theorem relativeFreeWittInverseVariable_eq (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) (s : σ) :
    relativeFreeWittInverseVariable D hp n s = MvPolynomial.X (s, n) -
      MvPolynomial.aeval (fun z : σ × Fin n => relativeFreeWittInverseVariable D hp z.2.val z.1)
        (relativeFreeWittGhostLowerPolynomial D hp s n) := by
  rw [relativeFreeWittInverseVariable, Nat.strongRec_eq]
  rfl

/-- 強帰納で構成した逆変数を指定する相対多項式代数射。 -/
def relativeFreeWittInverseMap (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    RelativeFreeDeltaRing (R := A) σ →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.aeval (fun z => relativeFreeWittInverseVariable D hp z.2 z.1)

/-- 逆代数射は全Witt係数を元のδ変数へ戻す。 -/
theorem relativeFreeWittInverseMap_coefficient (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    relativeFreeWittInverseMap D hp (relativeFreeWittGhostCoefficient D s n) =
      MvPolynomial.X (s, n) := by
  rw [relativeFreeWittGhostCoefficient_eq_X_add_lower D hp, map_add]
  simp only [relativeFreeWittInverseMap, MvPolynomial.aeval_X]
  rw [relativeFreeWittInverseVariable_eq]
  simp only [relativeFreeFiniteInitialPolynomialMap, MvPolynomial.aeval_rename]
  let t := MvPolynomial.aeval
    (fun z : σ × Fin n => relativeFreeWittInverseVariable D hp z.2.val z.1)
    (relativeFreeWittGhostLowerPolynomial D hp s n)
  change MvPolynomial.X (s, n) - t + t = MvPolynomial.X (s, n)
  exact sub_add_cancel _ _

/-- 元の座標代数射は全逆変数をδ変数へ戻す。 -/
theorem relativeFreeWittCoordinateMap_inverseVariable (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) (s : σ) :
    relativeFreeWittCoordinateMap D (relativeFreeWittInverseVariable D hp n s) =
      MvPolynomial.X (s, n) := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      rw [relativeFreeWittInverseVariable_eq, map_sub]
      have hx : relativeFreeWittCoordinateMap D (MvPolynomial.X (s, n)) =
          relativeFreeWittGhostCoefficient D s n := MvPolynomial.aeval_X _ _
      rw [hx, relativeFreeWittGhostCoefficient_eq_X_add_lower D hp]
      have he : relativeFreeWittCoordinateMap D
          (MvPolynomial.aeval
            (fun z : σ × Fin n => relativeFreeWittInverseVariable D hp z.2.val z.1)
            (relativeFreeWittGhostLowerPolynomial D hp s n)) =
          relativeFreeFiniteInitialPolynomialMap n σ A
            (relativeFreeWittGhostLowerPolynomial D hp s n) := by
        change ((relativeFreeWittCoordinateMap D).comp (MvPolynomial.aeval _)) _ = _
        rw [MvPolynomial.comp_aeval]
        have hv : (fun z : σ × Fin n => relativeFreeWittCoordinateMap D
            (relativeFreeWittInverseVariable D hp z.2.val z.1)) =
            fun z => (MvPolynomial.X (z.1, z.2.val) : RelativeFreeDeltaRing (R := A) σ) := by
          funext z
          exact ih z.2.val z.2.isLt z.1
        rw [hv]
        simp only [relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_eq_aeval]
        rfl
      rw [he]
      ring

/-- 逆座標代数射と座標代数射の合成は恒等。 -/
theorem relativeFreeWittInverseMap_comp_coordinateMap (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    (relativeFreeWittInverseMap D hp).comp (relativeFreeWittCoordinateMap (σ := σ) D) =
      AlgHom.id A _ := by
  apply MvPolynomial.algHom_ext
  intro z
  simp only [AlgHom.comp_apply, relativeFreeWittCoordinateMap, MvPolynomial.aeval_X,
    relativeFreeWittInverseMap_coefficient, AlgHom.id_apply]

/-- 座標代数射と逆座標代数射の合成も恒等。 -/
theorem relativeFreeWittCoordinateMap_comp_inverseMap (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    (relativeFreeWittCoordinateMap D).comp (relativeFreeWittInverseMap (σ := σ) D hp) =
      AlgHom.id A _ := by
  apply MvPolynomial.algHom_ext
  intro z
  simp only [AlgHom.comp_apply, relativeFreeWittInverseMap, MvPolynomial.aeval_X,
    relativeFreeWittCoordinateMap_inverseVariable, AlgHom.id_apply]

/-- 全Witt座標への三角形置換は、任意添字族での実際のA代数同型。 -/
def relativeFreeWittCoordinateEquiv (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    RelativeFreeDeltaRing (R := A) σ ≃ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  AlgEquiv.ofAlgHom (relativeFreeWittCoordinateMap D) (relativeFreeWittInverseMap D hp)
    (relativeFreeWittCoordinateMap_comp_inverseMap D hp)
    (relativeFreeWittInverseMap_comp_coordinateMap D hp)

/-- 代数同型は各δ変数を対応するWitt係数へ送る。 -/
@[simp] theorem relativeFreeWittCoordinateEquiv_X (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    relativeFreeWittCoordinateEquiv D hp (MvPolynomial.X (s, n)) =
      relativeFreeWittGhostCoefficient D s n := by
  exact MvPolynomial.aeval_X _ _

/-- 逆同型は各Witt係数を対応するδ変数へ戻す。 -/
@[simp] theorem relativeFreeWittCoordinateEquiv_symm_coefficient (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    (relativeFreeWittCoordinateEquiv D hp).symm (relativeFreeWittGhostCoefficient D s n) =
      MvPolynomial.X (s, n) :=
  relativeFreeWittInverseMap_coefficient D hp s n

end SerrePositivity.BhattScholze
