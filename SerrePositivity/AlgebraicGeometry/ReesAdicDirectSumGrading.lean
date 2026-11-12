module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectivePieces
public import SerrePositivity.AlgebraicGeometry.ReesProjectiveGrading
public import SerrePositivity.AlgebraicGeometry.ReesPolynomialBaseChange

/-!
概要：Rees 加群と各 IⁿM の直和の比較を、Proj 次数を保つ形で与える。
方針：既存のフィルトレーションの直和同値に、各段の多項式作用を入れる。
規約：全体の基底環上の作用は、多項式環を経由する作用に取る。
使われ方：Stacks 30.20.1 の Hⁱ に対応する Čech 版の Rees 比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R)

/-- 拡大イデアルによる I 進 Rees 加群の台。 -/
abbrev ReesAdicTotalModule :=
  ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
    (⊤ : Submodule (MvPolynomial ι R) M)).submodule

local instance (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n

local instance (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n

/-- 各 IⁿM の直和と Rees 加群の、多項式環上の線形同値。 -/
def reesAdicDirectSumPolynomialLinearEquiv :
    (⨁ n, reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) ≃ₗ[MvPolynomial ι R]
      ReesAdicTotalModule (ι := ι) (M := M) I :=
  reesFiltrationDirectSumLinearEquiv
    ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration ⊤)

/-- 基底環の作用は多項式環を経由させる。 -/
@[instance_reducible]
def reesAdicTotalBaseModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  Module.compHom _ (algebraMap R (MvPolynomial ι R))

local instance : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul

local instance : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I

local instance : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  IsScalarTower.of_compHom _ _ _

local instance : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul

local instance : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I

/-- 基底作用と基底 Rees 環の作用の両立性。 -/
theorem reesAdicTotalBaseModule_scalarTower :
    IsScalarTower R (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r p
  change reesMap I (I.map (algebraMap R (MvPolynomial ι R)))
      (algebraMap R (MvPolynomial ι R)) le_rfl (algebraMap R (reesAlgebra I) r) • p =
    (algebraMap R (MvPolynomial ι R) r) • p
  rw [reesMap_base, algebraMap_smul]

local instance : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

/-- 基底環上でも線形な Rees 加群の直和比較。 -/
def reesAdicDirectSumLinearEquiv :
    (⨁ n, reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) ≃ₗ[R]
      ReesAdicTotalModule (ι := ι) (M := M) I :=
  (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I).restrictScalars R

/-- 比較同値は、直和の第 n 成分を Rees の第 n 係数へ送る。 -/
theorem reesAdicDirectSumLinearEquiv_coeff
    (x : ⨁ n, reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) (n : ℕ) :
    (reesAdicDirectSumLinearEquiv (ι := ι) (M := M) I x).val.coeff n = (x n).val :=
  reesFiltrationAssemble_coeff
    ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
      (⊤ : Submodule (MvPolynomial ι R) M)) x n

variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- 直和の Proj 次数は各成分で判定する。 -/
def reesAdicDirectSumProjectivePiece (d : ℕ) :
    Submodule R (⨁ n, reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) where
  carrier := {x | ∀ n, (x n).val ∈ G d}
  zero_mem' := fun _n ↦ (G d).zero_mem
  add_mem' hx hy := fun n ↦ (G d).add_mem (hx n) (hy n)
  smul_mem' r _x hx := fun n ↦ (G d).smul_mem r (hx n)

/-- Rees 加群との比較は、直和の Proj 次数を保つ。 -/
theorem reesAdicDirectSumLinearEquiv_mem_iff (d : ℕ)
    (x : ⨁ n, reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :
    reesAdicDirectSumLinearEquiv (ι := ι) (M := M) I x ∈
        (reesProjectiveGrade (S := MvPolynomial ι R) I G d).restrictScalars R ↔
      x ∈ reesAdicDirectSumProjectivePiece (ι := ι) I G d := by
  change (reesAdicDirectSumLinearEquiv (ι := ι) (M := M) I x ∈
    reesProjectiveGrade (S := MvPolynomial ι R) I G d) ↔ ∀ n, (x n).val ∈ G d
  rw [mem_reesProjectiveGrade_iff]
  simp only [reesAdicDirectSumLinearEquiv_coeff]

end SerrePositivity.AlgebraicGeometry
