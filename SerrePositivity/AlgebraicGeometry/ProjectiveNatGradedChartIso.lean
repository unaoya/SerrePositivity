module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMapLaws

/-!
概要：次数成分を対応させる加群の同型を、標準開の図式の同型にする。
方針：同型とその逆の局所化を取り、合成則を用いる。
規約：元の係数環と多項式作用を区別する。
使われ方：filtered 余極限を、指定した実際の極限の係数環へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M N : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (e : M ≃ₗ[MvPolynomial ι R] N)
variable (he : ∀ n x, e x ∈ H n ↔ x ∈ G n)

include he in
/-- 指定した次数の同型は、逆写像も同じ次数を保つ。 -/
theorem projectiveNatGradedChartIso_inverse_mem (n : ℕ) (y : N) (hy : y ∈ H n) :
    e.symm y ∈ G n :=
  (he n _).mp (by simpa only [e.apply_symm_apply] using hy)

/-- 次数成分を保つ加群の同型が、標準開の係数図式に与える自然同型。 -/
def projectiveNatGradedChartIso (d : ℤ) :
    projectiveNatGradedModuleChartDiagram (ι := ι) G d ≅
      projectiveNatGradedModuleChartDiagram (ι := ι) H d where
  hom := projectiveNatGradedModuleChartMap G H e.toLinearMap
    (fun n x hx ↦ (he n x).mpr hx) d
  inv := projectiveNatGradedModuleChartMap H G e.symm.toLinearMap
    (projectiveNatGradedChartIso_inverse_mem G H e he) d
  hom_inv_id := by
    rw [projectiveNatGradedModuleChartMap_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext x
      exact e.symm_apply_apply x
    simpa only [h] using projectiveNatGradedModuleChartMap_id (ι := ι) G d
  inv_hom_id := by
    rw [projectiveNatGradedModuleChartMap_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext x
      exact e.apply_symm_apply x
    simpa only [h] using projectiveNatGradedModuleChartMap_id (ι := ι) H d

end SerrePositivity.AlgebraicGeometry
