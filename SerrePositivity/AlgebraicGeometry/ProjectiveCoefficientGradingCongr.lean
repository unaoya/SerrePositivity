module

public import SerrePositivity.AlgebraicGeometry.ProjectivePolynomialCoefficientMapNaturality

/-!
概要：基底環上の次数の族を等式で取り替えても、係数比較の自然性は保たれる。
方針：次数の族を変数として扱い、等式を消去して元の自然性へ戻す。
規約：次数の族に依存する GradedSMul の証明も一緒に移す。
使われ方：零延長と係数制限の交換で生じる、自然数次数の比較の型をそろえる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type} [DecidableEq ι] [Fintype ι]
local instance projectiveCoefficientGradeCongrPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance projectiveCoefficientGradeCongrPolynomialTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R B r) =
    MvPolynomial.map (algebraMap R B) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]

variable {M N : Type u} [AddCommGroup M] [Module R M] [Module B M]
variable [Module (MvPolynomial ι R) M] [Module (MvPolynomial ι B) M]
variable [IsScalarTower R B M] [IsScalarTower R (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι B) M] [IsScalarTower B (MvPolynomial ι B) M]
variable [IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) M]
variable [AddCommGroup N] [Module R N] [Module B N]
variable [Module (MvPolynomial ι R) N] [Module (MvPolynomial ι B) N]
variable [IsScalarTower R B N] [IsScalarTower R (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι B) N] [IsScalarTower B (MvPolynomial ι B) N]
variable [IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) N]
variable (G : ℤ → Submodule B M) (H : ℤ → Submodule B N)
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy B (projectivePolynomialDegree (ι := ι))) G]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
  (fun d ↦ (G d).restrictScalars R)]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy B (projectivePolynomialDegree (ι := ι))) H]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
  (fun d ↦ (H d).restrictScalars R)]
variable (f : M →ₗ[MvPolynomial ι B] N)
variable (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n)

/-- 基底環上の次数を、等しい別の族で書いた係数比較の同型。 -/
def projectivePolynomialCoefficientChartIsoOfGradeEq
    (K : ℤ → Submodule R M)
    [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) K]
    (hK : (fun n ↦ (G n).restrictScalars R) = K) (d : ℤ) :
    projectiveGradedModuleChartDiagram (ι := ι) K d ≅
      projectiveGradedModuleChartDiagram (R := B) (ι := ι) G d ⋙
        ModuleCat.restrictScalars (algebraMap R B) := by
  simpa only [hK] using
    projectiveGradedPolynomialCoefficientChangeChartIso (R := R) (ι := ι) G d

/-- 次数を等式で取り替えた係数比較も、次数を保つ加群写像に自然。 -/
theorem projectivePolynomialCoefficientChartIsoOfGradeEq_naturality
    (K : ℤ → Submodule R M) (L : ℤ → Submodule R N)
    [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) K]
    [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) L]
    (hK : (fun n ↦ (G n).restrictScalars R) = K)
    (hL : (fun n ↦ (H n).restrictScalars R) = L)
    (hfR : ∀ n, ∀ m ∈ K n, (f.restrictScalars (MvPolynomial ι R)) m ∈ L n) (d : ℤ) :
    projectiveGradedModuleChartMap (ι := ι) K L d
        (f.restrictScalars (MvPolynomial ι R)) hfR ≫
      (projectivePolynomialCoefficientChartIsoOfGradeEq (R := R) (ι := ι) H L hL d).hom =
    (projectivePolynomialCoefficientChartIsoOfGradeEq (R := R) (ι := ι) G K hK d).hom ≫
      Functor.whiskerRight (projectiveGradedModuleChartMap (R := B) (ι := ι) G H d f hf)
        (ModuleCat.restrictScalars (algebraMap R B)) := by
  subst K
  subst L
  with_unfolding_all exact
    projectiveGradedPolynomialCoefficientChangeChartIso_naturality G H f hf d

end SerrePositivity.AlgebraicGeometry
