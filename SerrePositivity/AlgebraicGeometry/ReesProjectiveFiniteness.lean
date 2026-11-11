module

public import SerrePositivity.AlgebraicGeometry.ReesProjectiveGrading
public import SerrePositivity.AlgebraicGeometry.ReesPolynomialBaseChange
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradingFromVariables
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedFiniteness

/-!
概要：基底 Rees 環上の Proj 次数付き Rees 加群に射影 Čech 有限性を適用する。
方針：多項式変数の作用を係数で計算し、既存の次数付き有限性へ渡す。
規約：有限変数の添字は Type に取る。Proj 次数と Rees 次数は別々に扱う。
この段では Rees 次数の直和との比較を主張しない。
使われ方：形式関数に使う Rees コホモロジーの有限性の第一段。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

universe u

variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance : Module (reesAlgebra I)
    ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
      (⊤ : Submodule (MvPolynomial ι R) M)).submodule :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I

local instance : Module (MvPolynomial ι (reesAlgebra I))
    ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
      (⊤ : Submodule (MvPolynomial ι R) M)).submodule :=
  Module.compHom _ (reesPolynomialBaseChange (ι := ι) I)

local instance : IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I))
    ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
      (⊤ : Submodule (MvPolynomial ι R) M)).submodule :=
  reesPolynomialBaseChange_module_scalarTower (ι := ι) I
    ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
      (⊤ : Submodule (MvPolynomial ι R) M)).submodule

/-- 多項式変数の作用は、Rees 係数ごとに元の変数を作用させる。 -/
theorem reesProjective_X_smul_coeff (i : ι)
    (p : ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
      (⊤ : Submodule (MvPolynomial ι R) M)).submodule) (n : ℕ) :
    ((MvPolynomial.X i : MvPolynomial ι (reesAlgebra I)) • p).val.coeff n =
      (MvPolynomial.X i : MvPolynomial ι R) • p.val.coeff n := by
  change (reesPolynomialBaseChange (ι := ι) I (MvPolynomial.X i) • p).val.coeff n = _
  rw [reesPolynomialBaseChange_X, algebraMap_smul]
  rfl

/-- 元の変数は Proj 次数を一つ上げ、基底 Rees 環上の次数付き作用を与える。 -/
theorem reesProjectivePolynomialGradedSMul :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (reesAlgebra I))
      (reesProjectiveGrade (S := MvPolynomial ι R) I G) := by
  refine projectiveGradedSMul_of_variables (B := reesAlgebra I) (ι := ι)
    (N := ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
      (⊤ : Submodule (MvPolynomial ι R) M)).submodule)
    (reesProjectiveGrade (S := MvPolynomial ι R) I G) ?_
  intro i j p hp
  apply (mem_reesProjectiveGrade_iff (S := MvPolynomial ι R) I G (j + 1) _).mpr
  intro n
  rw [reesProjective_X_smul_coeff]
  have hm := (mem_reesProjectiveGrade_iff (S := MvPolynomial ι R) I G j p).mp hp n
  have hXi : (MvPolynomial.X i : MvPolynomial ι R) ∈
      MvPolynomial.homogeneousSubmodule ι R 1 := MvPolynomial.isHomogeneous_X R i
  have hmul : (MvPolynomial.X i : MvPolynomial ι R) • p.val.coeff n ∈ G (1 + j) :=
    SetLike.GradedSMul.smul_mem (A := MvPolynomial.homogeneousSubmodule ι R) (B := G) hXi hm
  simpa only [add_comm] using hmul

-- Rees 環の部分環構造と、移した加群作用の同一視に多くの展開を要するため。
set_option maxHeartbeats 800000 in
/-- Rees 加群の Proj 標準開の全タプル Čech コホモロジーは、基底 Rees 環上有限生成。
これは Stacks 30.20.1 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesProjectiveFullCechHomology_finite [IsNoetherianRing R]
    [LinearOrder ι] [Fintype ι] [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    letI := reesProjectivePolynomialGradedSMul (ι := ι) I G
    Module.Finite (reesAlgebra I)
      ((fullCechComplex
        (projectiveNatGradedModuleChartDiagram (R := reesAlgebra I)
          (M := ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
            (⊤ : Submodule (MvPolynomial ι R) M)).submodule) (ι := ι)
          (reesProjectiveGrade (S := MvPolynomial ι R) I G) d)).homology q) := by
  let N := ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
    (⊤ : Submodule (MvPolynomial ι R) M)).submodule
  exact @projectiveNatGradedFullCechHomology_finite
    (reesAlgebra I) ι inferInstance inferInstance inferInstance inferInstance
    N inferInstance (reesExtendedModule (S := MvPolynomial ι R) (M := M) I)
    (Module.compHom N (reesPolynomialBaseChange (ι := ι) I))
    (reesPolynomialBaseChange_module_scalarTower (ι := ι) I N)
    (reesProjectiveGrade (S := MvPolynomial ι R) I G)
    (reesProjectiveGradeDecomposition (S := MvPolynomial ι R) I G)
    (reesProjectivePolynomialGradedSMul (ι := ι) I G)
    (reesAdicPolynomialModule_finite (ι := ι) I M) d q

end SerrePositivity.AlgebraicGeometry
