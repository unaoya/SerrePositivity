module

public import SerrePositivity.AlgebraicGeometry.ProjectivePolynomialCoefficientMapNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartAdditive

/-!
概要：次数族の同定を含む多項式係数変更の比較を、加群の射に自然にする。
方針：係数制限した次数族と指定次数族の等式を、比較同型と同時に輸送する。
規約：次数族の等式に依存する写像の型を明示する。
使われ方：自然数次数の零延長と係数制限を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type} [DecidableEq ι] [Fintype ι]
local instance projectiveTransportPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance projectiveTransportPolynomialTower :
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
variable (G : ℤ → Submodule B M) (GR : ℤ → Submodule R M)
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy B (projectivePolynomialDegree (ι := ι))) G]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) GR]

/-- 指定した次数族との同定を、恒等の加群写像による標準開の同型にする。 -/
def projectiveCoefficientChartIsoOfRestrictEq
    (eG : (fun n ↦ (G n).restrictScalars R) = GR) (d : ℤ) :
    projectiveGradedModuleChartDiagram (ι := ι) GR d ≅
      projectiveGradedModuleChartDiagram (R := B) (ι := ι) G d ⋙
        ModuleCat.restrictScalars (algebraMap R B) := by
  letI : SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (fun n ↦ (G n).restrictScalars R) := by
    rw [eG]
    infer_instance
  let raw := fun n ↦ (G n).restrictScalars R
  have he : ∀ n, ∀ x ∈ GR n, x ∈ raw n := by
    intro n x hx
    simpa only [raw, congrFun eG n] using hx
  have hi : ∀ n, ∀ x ∈ raw n, x ∈ GR n := by
    intro n x hx
    simpa only [raw, congrFun eG n] using hx
  let e : projectiveGradedModuleChartDiagram (ι := ι) GR d ≅
      projectiveGradedModuleChartDiagram (ι := ι) raw d :=
    { hom := projectiveGradedModuleChartMap GR raw d LinearMap.id he
      inv := projectiveGradedModuleChartMap raw GR d LinearMap.id hi
      hom_inv_id := by
        rw [projectiveGradedModuleChartMap_comp]
        exact projectiveGradedModuleChartMap_id (ι := ι) GR d
      inv_hom_id := by
        rw [projectiveGradedModuleChartMap_comp]
        exact projectiveGradedModuleChartMap_id (ι := ι) raw d }
  exact e ≪≫ projectiveGradedPolynomialCoefficientChangeChartIso
    (R := R) (B := B) (ι := ι) G d

variable (H : ℤ → Submodule B N) (HR : ℤ → Submodule R N)
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy B (projectivePolynomialDegree (ι := ι))) H]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) HR]

/-- 次数族の同定を含む比較も、次数を保つ加群の射に自然。 -/
theorem projectiveCoefficientChartIsoOfRestrictEq_naturality
    (eG : (fun n ↦ (G n).restrictScalars R) = GR)
    (eH : (fun n ↦ (H n).restrictScalars R) = HR)
    (f : M →ₗ[MvPolynomial ι B] N)
    (hf : ∀ n, ∀ x ∈ G n, f x ∈ H n)
    (hfR : ∀ n, ∀ x ∈ GR n, f x ∈ HR n) (d : ℤ) :
    projectiveGradedModuleChartMap (ι := ι) GR HR d
        (f.restrictScalars (MvPolynomial ι R)) hfR ≫
      (projectiveCoefficientChartIsoOfRestrictEq H HR eH d).hom =
    (projectiveCoefficientChartIsoOfRestrictEq G GR eG d).hom ≫
      Functor.whiskerRight (projectiveGradedModuleChartMap (R := B) (ι := ι) G H d f hf)
        (ModuleCat.restrictScalars (algebraMap R B)) := by
  subst GR
  subst HR
  simpa [projectiveCoefficientChartIsoOfRestrictEq, projectiveGradedModuleChartMap_id] using
    projectiveGradedPolynomialCoefficientChangeChartIso_naturality
      (R := R) (B := B) (ι := ι) G H f hf d

end SerrePositivity.AlgebraicGeometry
