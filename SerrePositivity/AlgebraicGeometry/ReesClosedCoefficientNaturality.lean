module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientModuleMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatCoefficientNaturality
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechModuleMap

/-!
概要：実際の M/JM の係数比較を、元の次数付き加群の射に自然にする。
方針：商係数の実際の商写像に、標準開と Čech の自然性を適用する。
規約：次数族の輸送には恒等写像を介する比較を使う。
使われ方：閉厚化の商環係数表示における形式関数の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M N : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (J : Ideal R) (f : M →ₗ[MvPolynomial ι R] N)
local instance : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) J 1
local instance : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) J 1
local instance : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J
local instance : IsScalarTower R (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficient_scalarTower (ι := ι) J
local instance : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J
local instance : IsScalarTower R (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_base_scalarTower (ι := ι) J
local instance : IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) J
local instance : Algebra (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J)) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).toAlgebra
local instance : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_scalarTower (ι := ι) J

local instance : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) J 1
local instance : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := N) J 1
local instance : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedCoefficientModule (ι := ι) (M := N) J
local instance : IsScalarTower R (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedCoefficient_scalarTower (ι := ι) (M := N) J
local instance : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) (M := N) J
local instance : IsScalarTower R (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_base_scalarTower (ι := ι) (M := N) J
local instance : IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) (M := N) J
local instance : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_scalarTower (ι := ι) (M := N) J


variable [LinearOrder ι] [Fintype ι]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable [DirectSum.Decomposition G] [DirectSum.Decomposition H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
local instance : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
    (reesClosedCoefficientPiece (ι := ι) J G) :=
  reesClosedCoefficientPieceGradedSMul (ι := ι) J G
local instance : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
    (fun n ↦ (reesClosedCoefficientPiece (ι := ι) J G n).restrictScalars R) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1
local instance : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
    (reesClosedCoefficientPiece (ι := ι) J H) :=
  reesClosedCoefficientPieceGradedSMul (ι := ι) J H
local instance : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
    (fun n ↦ (reesClosedCoefficientPiece (ι := ι) J H n).restrictScalars R) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J H 1

/-- 実際の閉厚化の標準開の、射に自然な商係数比較。 -/
def reesClosedCoefficientNaturalChartIso (d : ℤ) :=
  projectiveNatCoefficientChartIso (R := R) (B := R ⧸ J) (ι := ι)
    (reesClosedCoefficientPiece (ι := ι) J G) d

/-- 実際の閉厚化の Čech コホモロジーの、射に自然な商係数比較。
原典 Stacks 30.20.5 の Hⁱ に対応する Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedCoefficientNaturalCechIso (d : ℤ) (q : ℕ) :=
  projectiveNatCoefficientCechIso (R := R) (B := R ⧸ J) (ι := ι)
    (reesClosedCoefficientPiece (ι := ι) J G) d q

variable (hf : ∀ n, ∀ x ∈ G n, f x ∈ H n)

/-- 次数付き加群の射が誘導する、商係数の閉厚化の標準開の射。 -/
def reesClosedCoefficientModuleChartMap (d : ℤ) :=
  projectiveNatGradedModuleChartMap (R := R ⧸ J) (ι := ι)
    (reesClosedCoefficientPiece (ι := ι) J G) (reesClosedCoefficientPiece (ι := ι) J H)
    (reesClosedCoefficientModuleMap J f)
    (reesClosedCoefficientModuleMap_preservesPiece J f G H hf) d

/-- 商係数の標準開比較は、実際の閉厚化の加群写像と可換。 -/
theorem reesClosedCoefficientNaturalChartIso_naturality (d : ℤ) :
    reesAdicProjectiveClosedCechModuleChartMap J G H f hf 1 d ≫
        (reesClosedCoefficientNaturalChartIso (ι := ι) J H d).hom =
      (reesClosedCoefficientNaturalChartIso (ι := ι) J G d).hom ≫
        Functor.whiskerRight (reesClosedCoefficientModuleChartMap J f G H hf d)
          (ModuleCat.restrictScalars (Ideal.Quotient.mk J)) := by
  have h := projectiveNatCoefficientChartIso_naturality
    (R := R) (B := R ⧸ J) (ι := ι)
    (reesClosedCoefficientPiece (ι := ι) J G) (reesClosedCoefficientPiece (ι := ι) J H)
    (reesClosedCoefficientModuleMap J f)
    (reesClosedCoefficientModuleMap_preservesPiece J f G H hf) d
  convert h using 1 <;> rfl


/-- 元の次数付き加群の射から得られる、商係数の閉厚化の Čech 写像。 -/
def reesClosedCoefficientModuleCechMap (d : ℤ) (q : ℕ) :=
  projectiveNatGradedModuleCechHomologyMap (R := R ⧸ J) (ι := ι)
    (reesClosedCoefficientPiece (ι := ι) J G) (reesClosedCoefficientPiece (ι := ι) J H)
    (reesClosedCoefficientModuleMap J f)
    (reesClosedCoefficientModuleMap_preservesPiece J f G H hf) d q

/-- 商係数の Čech 比較は、実際の閉厚化の加群写像と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedCoefficientNaturalCechIso_naturality (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechModuleMap J G H f hf 1 d q ≫
        (reesClosedCoefficientNaturalCechIso (ι := ι) J H d q).hom =
      (reesClosedCoefficientNaturalCechIso (ι := ι) J G d q).hom ≫
        (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).map
          (reesClosedCoefficientModuleCechMap J f G H hf d q) := by
  have h := projectiveNatCoefficientCechIso_naturality
    (R := R) (B := R ⧸ J) (ι := ι)
    (reesClosedCoefficientPiece (ι := ι) J G) (reesClosedCoefficientPiece (ι := ι) J H)
    (reesClosedCoefficientModuleMap J f)
    (reesClosedCoefficientModuleMap_preservesPiece J f G H hf) d q
  convert h using 1 <;> rfl

end SerrePositivity.AlgebraicGeometry
