module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectivePieces
public import Mathlib.RingTheory.Filtration

/-!
概要：Iⁱ の元による作用を、IʲM から Iⁱ⁺ʲM への線形写像にする。
方針：拡大イデアルの安定フィルトレーションの乗法性を使う。
規約：Rees 次数は i だけ増え、Proj 次数は変わらない。
使われ方：Rees の Čech 比較における斉次な係数作用の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R)

local instance reesDegreeShiftPolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n

/-- Iⁱ の元の作用は、IʲM の元を Iⁱ⁺ʲM に送る。 -/
theorem reesAdicProjectiveDegreeShift_mem (i j : ℕ) (a : R) (ha : a ∈ I ^ i)
    (m : reesAdicProjectiveSubmodule (ι := ι) (M := M) I j) :
    a • m.val ∈ reesAdicProjectiveSubmodule (ι := ι) (M := M) I (i + j) := by
  have ha' : algebraMap R (MvPolynomial ι R) a ∈
      (I.map (algebraMap R (MvPolynomial ι R))) ^ i := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  have h := ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
    (⊤ : Submodule (MvPolynomial ι R) M)).pow_smul_le i j
      (Submodule.smul_mem_smul ha' m.property)
  change (algebraMap R (MvPolynomial ι R) a) • m.val ∈
    (I.map (algebraMap R (MvPolynomial ι R))) ^ (i + j) •
      (⊤ : Submodule (MvPolynomial ι R) M) at h
  change a • m.val ∈ (I.map (algebraMap R (MvPolynomial ι R))) ^ (i + j) •
    (⊤ : Submodule (MvPolynomial ι R) M)
  simpa only [algebraMap_smul] using h

/-- Iⁱ の元による、多項式環上線形な Rees 次数 i の写像。 -/
def reesAdicProjectiveDegreeShift (i j : ℕ) (a : R) (ha : a ∈ I ^ i) :
    reesAdicProjectiveSubmodule (ι := ι) (M := M) I j →ₗ[MvPolynomial ι R]
      reesAdicProjectiveSubmodule (ι := ι) (M := M) I (i + j) where
  toFun m := ⟨a • m.val, reesAdicProjectiveDegreeShift_mem I i j a ha m⟩
  map_add' m n := Subtype.ext (smul_add a m.val n.val)
  map_smul' p m := Subtype.ext (smul_comm a p m.val)

/-- 次数を移す写像の、もとの加群での値。 -/
@[simp] theorem reesAdicProjectiveDegreeShift_val (i j : ℕ) (a : R) (ha : a ∈ I ^ i)
    (m : reesAdicProjectiveSubmodule (ι := ι) (M := M) I j) :
    (reesAdicProjectiveDegreeShift I i j a ha m).val = a • m.val := rfl

/-- 基底環の係数による作用は、Proj 次数を保つ。 -/
theorem reesAdicProjectiveDegreeShift_preservesPiece
    (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
    (i j d : ℕ) (a : R) (ha : a ∈ I ^ i)
    (m : reesAdicProjectiveSubmodule (ι := ι) (M := M) I j)
    (hm : m ∈ reesAdicProjectivePiece (ι := ι) I G j d) :
    reesAdicProjectiveDegreeShift I i j a ha m ∈
      reesAdicProjectivePiece (ι := ι) I G (i + j) d := by
  exact (G d).smul_mem a hm

end SerrePositivity.AlgebraicGeometry
