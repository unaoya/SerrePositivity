module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveDegreeShift
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartScalarAction

/-!
概要：I 進フィルトレーションの遷移と、元の加群への包含を多項式環上線形にする。
方針：イデアルの冪の減少性を使い、すべての写像を元の加群での値から定める。
規約：遷移は IⁱM から IʲM（j≤i）へ向かう。
使われ方：Čech コホモロジーの像フィルトレーションと、核の遷移の零化への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R)

local instance reesTransitionPolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n

/-- 各 IⁿM から元の加群への包含。 -/
def reesAdicProjectiveToModule (n : ℕ) :
    reesAdicProjectiveSubmodule (ι := ι) (M := M) I n →ₗ[MvPolynomial ι R] M where
  toFun m := m.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- I 進部分加群は、指数が大きいほど小さい。 -/
theorem reesAdicProjectiveSubmodule_antitone {i j : ℕ} (h : j ≤ i) :
    reesAdicProjectiveSubmodule (ι := ι) (M := M) I i ≤
      reesAdicProjectiveSubmodule (ι := ι) (M := M) I j := by
  intro m hm
  exact Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl hm

/-- IⁱM から IʲM への遷移（j≤i）。 -/
def reesAdicProjectiveTransition (i j : ℕ) (h : j ≤ i) :
    reesAdicProjectiveSubmodule (ι := ι) (M := M) I i →ₗ[MvPolynomial ι R]
      reesAdicProjectiveSubmodule (ι := ι) (M := M) I j where
  toFun m := ⟨m.val, reesAdicProjectiveSubmodule_antitone I h m.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 遷移の元の加群での値は変わらない。 -/
@[simp] theorem reesAdicProjectiveTransition_val (i j : ℕ) (h : j ≤ i)
    (m : reesAdicProjectiveSubmodule (ι := ι) (M := M) I i) :
    (reesAdicProjectiveTransition (ι := ι) (M := M) I i j h m).val = m.val := rfl

/-- 遷移と元の加群への包含は可換。 -/
theorem reesAdicProjectiveToModule_transition (i j : ℕ) (h : j ≤ i) :
    (reesAdicProjectiveToModule (ι := ι) (M := M) I j).comp
      (reesAdicProjectiveTransition (ι := ι) (M := M) I i j h) =
    reesAdicProjectiveToModule (ι := ι) (M := M) I i := rfl

/-- 遷移の合成は遷移に一致。 -/
theorem reesAdicProjectiveTransition_comp (i j k : ℕ) (hij : j ≤ i) (hjk : k ≤ j) :
    (reesAdicProjectiveTransition (ι := ι) (M := M) I j k hjk).comp
      (reesAdicProjectiveTransition (ι := ι) (M := M) I i j hij) =
    reesAdicProjectiveTransition (ι := ι) (M := M) I i k (hjk.trans hij) := rfl

/-- 次数移動後に元の加群へ含めると、基底係数のスカラー写像になる。 -/
theorem reesAdicProjectiveToModule_degreeShift
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) :
    (reesAdicProjectiveToModule (ι := ι) (M := M) I (i + j)).comp
      (reesAdicProjectiveDegreeShift (ι := ι) (M := M) I i j a ha) =
    (projectiveBaseScalarLinearMap (S := MvPolynomial ι R) a).comp
      (reesAdicProjectiveToModule (ι := ι) (M := M) I j) := rfl

/-- Iⁿ の係数の作用は、元の加群から IⁿM への写像を与える。 -/
def reesAdicProjectiveCoefficientLift (n : ℕ) (a : R) (ha : a ∈ I ^ n) :
    M →ₗ[MvPolynomial ι R] reesAdicProjectiveSubmodule (ι := ι) (M := M) I n where
  toFun m := ⟨a • m, by
    have ha' : algebraMap R (MvPolynomial ι R) a ∈
        (I.map (algebraMap R (MvPolynomial ι R))) ^ n := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    have hm := Submodule.smul_mem_smul ha' (show m ∈ (⊤ : Submodule (MvPolynomial ι R) M) from
      Submodule.mem_top)
    change a • m ∈ (I.map (algebraMap R (MvPolynomial ι R))) ^ n •
      (⊤ : Submodule (MvPolynomial ι R) M)
    simpa only [algebraMap_smul] using hm⟩
  map_add' m m' := Subtype.ext (smul_add a m m')
  map_smul' p m := Subtype.ext (smul_comm a p m)

/-- 係数の持ち上げと包含の合成は、元の加群のスカラー作用。 -/
theorem reesAdicProjectiveToModule_coefficientLift (n : ℕ) (a : R) (ha : a ∈ I ^ n) :
    (reesAdicProjectiveToModule (ι := ι) (M := M) I n).comp
      (reesAdicProjectiveCoefficientLift (ι := ι) (M := M) I n a ha) =
    projectiveBaseScalarLinearMap (S := MvPolynomial ι R) a := rfl

/-- 係数が Iⁿ に入れば、次数移動からの遷移は元の加群を経由する。 -/
theorem reesAdicProjectiveTransition_degreeShift_factor
    (i j n : ℕ) (hn : n ≤ i) (a : R) (ha : a ∈ I ^ i) :
    (reesAdicProjectiveTransition (ι := ι) (M := M) I (i + j) n
        (hn.trans (Nat.le_add_right i j))).comp
      (reesAdicProjectiveDegreeShift (ι := ι) (M := M) I i j a ha) =
    (reesAdicProjectiveCoefficientLift (ι := ι) (M := M) I n a
        ((Ideal.pow_le_pow_right hn) ha)).comp
      (reesAdicProjectiveToModule (ι := ι) (M := M) I j) := rfl

section Grading
variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- 元の加群への包含は Proj 次数を保つ。 -/
theorem reesAdicProjectiveToModule_preservesPiece (n d : ℕ)
    (m : reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (hm : m ∈ reesAdicProjectivePiece (ι := ι) I G n d) :
    reesAdicProjectiveToModule (ι := ι) (M := M) I n m ∈ G d := hm

/-- 遷移は Proj 次数を保つ。 -/
theorem reesAdicProjectiveTransition_preservesPiece (i j d : ℕ) (h : j ≤ i)
    (m : reesAdicProjectiveSubmodule (ι := ι) (M := M) I i)
    (hm : m ∈ reesAdicProjectivePiece (ι := ι) I G i d) :
    reesAdicProjectiveTransition (ι := ι) (M := M) I i j h m ∈
      reesAdicProjectivePiece (ι := ι) I G j d := hm

/-- 係数の持ち上げは Proj 次数を保つ。 -/
theorem reesAdicProjectiveCoefficientLift_preservesPiece (n d : ℕ) (a : R) (ha : a ∈ I ^ n)
    (m : M) (hm : m ∈ G d) :
    reesAdicProjectiveCoefficientLift (ι := ι) (M := M) I n a ha m ∈
      reesAdicProjectivePiece (ι := ι) I G n d :=
  (G d).smul_mem a hm

end Grading
end SerrePositivity.AlgebraicGeometry
