module

public import SerrePositivity.AlgebraicGeometry.ReesAdicDirectSumGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSumComponents

/-!
概要：Rees 加群の局所化を、各 IⁿM の局所化の直和と比較する。
方針：Rees 加群の係数の直和同値を局所化し、局所化と直和を交換する。
規約：ここでは元の多項式環で局所化し、Proj 次数の制限は後で行う。
使われ方：射影標準開の Rees–Čech 比較の、周囲の加群の同値。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum
attribute [local instance] LocalizedModule.moduleOfIsLocalization
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R)

local instance (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n

/-- 任意の多項式の冪による局所化での、Rees 加群と次数成分の直和の比較。 -/
def reesAdicLocalizedDirectSumLinearEquiv (f : MvPolynomial ι R) :
    LocalizedModule (Submonoid.powers f) (ReesAdicTotalModule (ι := ι) (M := M) I) ≃ₗ[MvPolynomial ι R]
      ⨁ n, LocalizedModule (Submonoid.powers f)
        (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (@projectiveLocalizedModuleCongr (MvPolynomial ι R) inferInstance (Submonoid.powers f)
    (ReesAdicTotalModule (ι := ι) (M := M) I)
    (⨁ n, reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    inferInstance inferInstance inferInstance inferInstance
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I).symm).trans
      (@projectiveLocalizedDirectSumLinearEquiv (MvPolynomial ι R) ℕ inferInstance inferInstance
        (Submonoid.powers f) (fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
        (fun n ↦ inferInstance) (fun n ↦ inferInstance))

/-- 比較は分母を保ち、分子をその Rees 次数成分へ送る。 -/
theorem reesAdicLocalizedDirectSumLinearEquiv_mk_component (f : MvPolynomial ι R)
    (p : ReesAdicTotalModule (ι := ι) (M := M) I) (s : Submonoid.powers f) (n : ℕ) :
    (reesAdicLocalizedDirectSumLinearEquiv (ι := ι) (M := M) I f
      (LocalizedModule.mk p s)) n =
        LocalizedModule.mk
          ((reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I).symm p n) s := by
  change (projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f)
    (fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
      (projectiveLocalizedModuleCongr (Submonoid.powers f)
        (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I).symm
          (LocalizedModule.mk p s))) n = _
  rw [projectiveLocalizedModuleCongr_mk, projectiveLocalizedDirectSumLinearEquiv_mk_component]

end SerrePositivity.AlgebraicGeometry
