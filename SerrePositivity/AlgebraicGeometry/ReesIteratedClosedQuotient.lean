module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotient
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
概要：実際の二重の閉厚化 (M/JM)/Iⁿ(M/JM) を、一つの商として比較する。
方針：全射によるイデアル作用の像と、加群の第三同型定理を使う。
規約：分母の和は多項式環上の部分加群の和とし、flat 性は仮定しない。
使われ方：閉厚化後の Čech 計算を M/(JM+IⁿM) で表す際の係数比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I J : Ideal R)
local instance iteratedClosedModule : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) J 1
local instance iteratedClosedTower : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) J 1
local instance iteratedClosedQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n

/-- 多項式環上で見た、基底イデアルの拡大冪による部分加群。 -/
abbrev reesAdicProjectivePolynomialSubmodule (A : Ideal R) (n : ℕ) :
    Submodule (MvPolynomial ι R) M :=
  (A.map (algebraMap R (MvPolynomial ι R))) ^ n • ⊤

/-- 全射 M→M/JM による IⁿM の像は、Iⁿ(M/JM) に等しい。 -/
theorem reesIteratedClosedQuotient_submodule_image (n : ℕ) :
    (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n).map
      (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1).mkQ =
    reesAdicProjectivePolynomialSubmodule (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n := by
  unfold reesAdicProjectivePolynomialSubmodule
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

/-- (M/JM)/Iⁿ(M/JM) と M/(JM+IⁿM) の、多項式環上線形な同型。 -/
def reesIteratedClosedQuotientLinearEquiv (n : ℕ) :
    reesAdicProjectiveQuotient (ι := ι)
        (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n ≃ₗ[MvPolynomial ι R]
      M ⧸ (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
        reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n) :=
  (Submodule.quotEquivOfEq
    (reesAdicProjectivePolynomialSubmodule (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n)
    ((reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n).map
      (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1).mkQ)
    (reesIteratedClosedQuotient_submodule_image (ι := ι) (M := M) I J n).symm).trans
    (Submodule.quotientQuotientEquivQuotientSup
      (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1)
      (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n))

/-- 二重閉厚化の同型は、元の加群の代表をそのまま単一の剰余類に送る。 -/
@[simp] theorem reesIteratedClosedQuotientLinearEquiv_mk_mk (n : ℕ) (m : M) :
    reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J n
      (Submodule.Quotient.mk (Submodule.Quotient.mk m)) = Submodule.Quotient.mk m := rfl

end SerrePositivity.AlgebraicGeometry
