module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechScalarAction

/-!
概要：基底環の係数作用を、標準開の係数図式と Čech コホモロジーへ渡す。
方針：分数の分子の作用を計算し、既存の Čech スカラー作用の公式に接続する。
規約：係数環は固定し、基底環の元は多項式環上線形な自己写像として作用させる。
使われ方：Rees の B[X] 上の計算で、b∈B の作用を b 倍の恒等写像と同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

section Module
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- 基底環の係数による、係数環上線形な自己写像。 -/
def projectiveBaseScalarLinearMap (r : R) : M →ₗ[S] M where
  toFun m := r • m
  map_add' m n := smul_add r m n
  map_smul' s m := smul_comm r s m

/-- 指定次数の局所化で、基底係数の写像は既存のスカラー作用に一致。 -/
theorem projectiveGradedAwayMap_baseScalar (p : S) (V : ℕ → Submodule R M) (r : R) :
    projectiveGradedAwayMap p V V (projectiveBaseScalarLinearMap (S := S) r)
        (fun n m hm ↦ (V n).smul_mem r hm) =
      r • (LinearMap.id : projectiveGradedAway p V →ₗ[R] projectiveGradedAway p V) := by
  have h (x : LocalizedModule (Submonoid.powers p) M) :
      IsLocalizedModule.map (Submonoid.powers p)
          (LocalizedModule.mkLinearMap (Submonoid.powers p) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers p) M)
          (projectiveBaseScalarLinearMap (S := S) r) x = r • x := by
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      rw [IsLocalizedModule.map_LocalizedModules]
      exact (LocalizedModule.smul'_mk r m s).symm
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact h z.val

end Module

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (G : ℤ → Submodule R M)
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) G]

/-- 基底の係数による標準開の図式の自己写像は、恒等自然変換のスカラー倍。 -/
theorem projectiveGradedModuleChartMap_baseScalar (r : R) (d : ℤ) :
    projectiveGradedModuleChartMap (ι := ι) G G d
        (projectiveBaseScalarLinearMap (S := MvPolynomial ι R) r)
        (fun n m hm ↦ (G n).smul_mem r hm) =
      r • 𝟙 (projectiveGradedModuleChartDiagram (ι := ι) G d) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  exact projectiveGradedAwayMap_baseScalar (projectiveLaurentDenominator R T)
    (fun n ↦ G (d + n • (T.card : ℤ))) r

/-- 基底係数の自己写像が誘導する Čech コホモロジー写像は、既存のスカラー作用。
原典 Stacks 30.20.1 の Hⁱ の Rees 作用に対応する Čech 版の式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveGradedModuleCechHomologyMap_baseScalar (r : R) (d : ℤ) (q : ℕ) :
    HomologicalComplex.homologyMap
        (fullCechComplexMap (projectiveGradedModuleChartMap (ι := ι) G G d
          (projectiveBaseScalarLinearMap (S := MvPolynomial ι R) r)
          (fun n m hm ↦ (G n).smul_mem r hm))) q =
      r • 𝟙 ((fullCechComplex (projectiveGradedModuleChartDiagram (ι := ι) G d)).homology q) := by
  rw [projectiveGradedModuleChartMap_baseScalar]
  exact projectiveCechHomologyMap_smul_id r _ q

end SerrePositivity.AlgebraicGeometry
