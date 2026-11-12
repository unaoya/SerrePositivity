module

public import SerrePositivity.AlgebraicGeometry.ReesClosedTensorChart
public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientNaturality

/-!
概要：テンソルによる閉厚化の表示を、元の加群写像に自然にする。
方針：純テンソルの元と商への射影で比較し、標準開の合成則へ送る。
規約：商係数への底変換の平坦性は仮定しない。
使われ方：既存の閉厚化・I 進系の自然性と、実際のテンソル表示を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct
universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (J : Ideal R)
local instance reesClosedTensorNaturalOldPolynomialModule : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) J 1
local instance reesClosedTensorNaturalOldPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) J 1
local instance reesClosedTensorNaturalSourceCoefficientModule :
    Module (R ⧸ J) (M ⊗[R] (R ⧸ J)) := tensorRightCoefficientModule
local instance reesClosedTensorNaturalSourcePolynomialModule :
    Module (MvPolynomial ι (R ⧸ J)) (M ⊗[R] (R ⧸ J)) := projectiveTensorPolynomialModule
local instance reesClosedTensorNaturalSourcePolynomialTower :
    IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J)) (M ⊗[R] (R ⧸ J)) :=
  projectiveTensorPolynomial_coefficient_scalarTower
local instance reesClosedTensorNaturalTargetCoefficientModule : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J
local instance reesClosedTensorNaturalTargetPolynomialModule : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J
local instance reesClosedTensorNaturalTargetPolynomialTower :
    IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) J

variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]


variable {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (H : ℕ → Submodule R N) [DirectSum.Decomposition H]
variable (f : M →ₗ[MvPolynomial ι R] N)

/-- テンソルと閉厚化の比較は、元の多項式加群の射と可換。 -/
theorem reesClosedTensorEquiv_naturality (z : M ⊗[R] (R ⧸ J)) :
    reesClosedTensorPolynomialEquiv (ι := ι) J (projectiveTensorPolynomialMap (B := R ⧸ J) f z) =
      reesClosedCoefficientModuleMap J f (reesClosedTensorPolynomialEquiv (ι := ι) J z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m b =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    change reesClosedTensorEquiv (ι := ι) J
      (projectiveTensorPolynomialMap (B := R ⧸ J) f (m ⊗ₜ[R] Ideal.Quotient.mk J r)) = _
    rw [projectiveTensorPolynomialMap_tmul, reesClosedTensorEquiv_tmul_mk]
    change reesAdicProjectiveQuotientProjection (ι := ι) J 1 (r • f m) =
      reesClosedCoefficientModuleMap J f
        (reesClosedTensorEquiv (ι := ι) J (m ⊗ₜ[R] Ideal.Quotient.mk J r))
    rw [reesClosedTensorEquiv_tmul_mk]
    change reesAdicProjectiveQuotientProjection (ι := ι) J 1 (r • f m) =
      reesAdicProjectiveQuotientMap J f 1
        (reesAdicProjectiveQuotientProjection (ι := ι) J 1 (r • m))
    rw [show reesAdicProjectiveQuotientMap J f 1
        (reesAdicProjectiveQuotientProjection (ι := ι) J 1 (r • m)) =
      reesAdicProjectiveQuotientProjection (ι := ι) J 1 (f (r • m)) from
        LinearMap.congr_fun (reesAdicProjectiveQuotientMap_projection J f 1) (r • m)]
    congr 1
    exact ((f.restrictScalars R).map_smul r m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (hf : ∀ j, ∀ m ∈ G j, f m ∈ H j)
local instance reesClosedTensorNaturalSourceGradedAction :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
      (projectiveTensorPiece (B := R ⧸ J) G) := projectiveTensorPiece_gradedSMul (ι := ι) G
local instance reesClosedTensorNaturalTargetGradedAction :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
      (reesClosedCoefficientPiece (ι := ι) J G) :=
  reesClosedCoefficientPieceGradedSMul (ι := ι) J G

/-- R/J による標準開の表示の同型は、次数を保つ加群写像に自然。 -/
theorem reesClosedTensorChartIso_naturality (d : ℤ) :
    projectiveTensorGradedModuleChartMap (B := R ⧸ J) G H f hf d ≫
        (reesClosedTensorChartIso (ι := ι) J H d).hom =
      (reesClosedTensorChartIso (ι := ι) J G d).hom ≫
        reesClosedCoefficientModuleChartMap J f G H hf d := by
  simp only [projectiveTensorGradedModuleChartMap, reesClosedTensorChartIso,
    projectiveNatGradedModuleChartIso, reesClosedCoefficientModuleChartMap]
  rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
  congr 1
  apply LinearMap.ext
  intro z
  exact reesClosedTensorEquiv_naturality (ι := ι) J f z

/-- R/J の実際の閉厚化の Čech 比較は、次数を保つ加群写像に自然。
原典 Stacks 30.20.4–30.20.5 の Hⁱ の閉厚化・形式関数の自然性に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedTensorCechIso_naturality (d : ℤ) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} (R ⧸ J)) (.up ℕ) q).map
        (fullCechComplexMap (projectiveTensorGradedModuleChartMap (B := R ⧸ J) G H f hf d)) ≫
      (reesClosedTensorCechIso (ι := ι) J H d q).hom =
    (reesClosedTensorCechIso (ι := ι) J G d q).hom ≫
      reesClosedCoefficientModuleCechMap J f G H hf d q := by
  let K := fullCechComplexFunctor (R := R ⧸ J) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} (R ⧸ J)) (.up ℕ) q
  change K.map (projectiveTensorGradedModuleChartMap (B := R ⧸ J) G H f hf d) ≫
      K.map (reesClosedTensorChartIso (ι := ι) J H d).hom =
    K.map (reesClosedTensorChartIso (ι := ι) J G d).hom ≫
      K.map (reesClosedCoefficientModuleChartMap J f G H hf d)
  rw [← K.map_comp, reesClosedTensorChartIso_naturality, K.map_comp]

end SerrePositivity.AlgebraicGeometry
