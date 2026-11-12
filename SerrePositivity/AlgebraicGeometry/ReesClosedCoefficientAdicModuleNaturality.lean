module

public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicFormalFunctionsNaturality
public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientAdicFormalFunctions

/-!
概要：M/JM の商係数の I 進互換族と形式関数を、任意の元の加群写像に自然にする。
方針：実際の M/JM→N/JN の写像に一般の自然性を適用し、既存の型と照合する。
規約：I と J を区別し、係数環 R/J は I 進系を通して固定する。
使われ方：閉厚化との整合性を、射影だけでなく任意の射に対して供給する。
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
variable (I : Ideal R)
variable (J : Ideal R) (f : M →ₗ[MvPolynomial ι R] N)
local instance closedAdicModuleNatLocal0 : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) J 1
local instance closedAdicModuleNatLocal1 : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) J 1
local instance closedAdicModuleNatLocal2 : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J
local instance closedAdicModuleNatLocal3 : IsScalarTower R (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficient_scalarTower (ι := ι) J
local instance closedAdicModuleNatLocal4 : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J
local instance closedAdicModuleNatLocal5 : IsScalarTower R (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_base_scalarTower (ι := ι) J
local instance closedAdicModuleNatLocal6 : IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) J
local instance closedAdicModuleNatLocal7 : Algebra (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J)) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).toAlgebra
local instance closedAdicModuleNatLocal8 : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_scalarTower (ι := ι) J

local instance closedAdicModuleNatLocal9 : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) J 1
local instance closedAdicModuleNatLocal10 : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := N) J 1
local instance closedAdicModuleNatLocal11 : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedCoefficientModule (ι := ι) (M := N) J
local instance closedAdicModuleNatLocal12 : IsScalarTower R (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedCoefficient_scalarTower (ι := ι) (M := N) J
local instance closedAdicModuleNatLocal13 : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) (M := N) J
local instance closedAdicModuleNatLocal14 : IsScalarTower R (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_base_scalarTower (ι := ι) (M := N) J
local instance closedAdicModuleNatLocal15 : IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) (M := N) J
local instance closedAdicModuleNatLocal16 : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  reesClosedPolynomialCoefficient_scalarTower (ι := ι) (M := N) J


variable [LinearOrder ι] [Fintype ι]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable [DirectSum.Decomposition G] [DirectSum.Decomposition H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
local instance closedAdicModuleNatLocal17 : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
    (reesClosedCoefficientPiece (ι := ι) J G) :=
  reesClosedCoefficientPieceGradedSMul (ι := ι) J G
local instance closedAdicModuleNatLocal18 : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
    (fun n ↦ (reesClosedCoefficientPiece (ι := ι) J G n).restrictScalars R) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1
local instance closedAdicModuleNatLocal19 : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
    (reesClosedCoefficientPiece (ι := ι) J H) :=
  reesClosedCoefficientPieceGradedSMul (ι := ι) J H
local instance closedAdicModuleNatLocal20 : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
    (fun n ↦ (reesClosedCoefficientPiece (ι := ι) J H n).restrictScalars R) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J H 1

local instance closedAdicModuleNatSurjective :
    Fact (Function.Surjective (algebraMap R (R ⧸ J))) := ⟨Ideal.Quotient.mk_surjective⟩
local instance closedAdicModuleNatSourceDecomp :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1
local instance closedAdicModuleNatSourceDecompRestrict : DirectSum.Decomposition
    (fun a ↦ (reesClosedCoefficientPiece (ι := ι) J G a).restrictScalars R) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1
local instance closedAdicModuleNatSourceGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1
local instance closedAdicModuleNatTargetDecomp :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) J H 1) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J H 1
local instance closedAdicModuleNatTargetDecompRestrict : DirectSum.Decomposition
    (fun a ↦ (reesClosedCoefficientPiece (ι := ι) J H a).restrictScalars R) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J H 1
local instance closedAdicModuleNatTargetGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) J H 1) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J H 1
variable (hf : ∀ d, ∀ m ∈ G d, f m ∈ H d)

/-- 実際の M/JM→N/JN が誘導する、商係数の I 進 Čech 互換族の写像。 -/
def reesClosedCoefficientAdicModuleFamiliesMap (d : ℤ) (q : ℕ) :=
  reesCoefficientAdicRestrictedCechFamiliesMap (R := R) (B := R ⧸ J) (ι := ι) I
    (reesClosedCoefficientPiece (ι := ι) J G) (reesClosedCoefficientPiece (ι := ι) J H)
    (reesClosedCoefficientModuleMap J f)
    (reesClosedCoefficientModuleMap_preservesPiece J f G H hf) d q

/-- 実際の M/JM→N/JN が各 I 進段で誘導する、商係数の Čech 写像。 -/
def reesClosedCoefficientAdicModuleCechMap (n : ℕ) (d : ℤ) (q : ℕ) :=
  reesCoefficientAdicRestrictedCechModuleMap (R := R) (B := R ⧸ J) (ι := ι) I
    (reesClosedCoefficientPiece (ι := ι) J G) (reesClosedCoefficientPiece (ι := ι) J H)
    (reesClosedCoefficientModuleMap J f)
    (reesClosedCoefficientModuleMap_preservesPiece J f G H hf) n d q

/-- 実際の閉厚化の各 I 進段の係数比較は、任意の元の次数付き加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedCoefficientAdicCechIso_module_naturality (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechModuleMap I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1)
        (reesAdicProjectiveQuotientPiece (ι := ι) J H 1)
        (reesAdicProjectiveQuotientMap J f 1)
        (reesAdicProjectiveQuotientMap_preservesPiece J f G H hf 1) n d q ≫
      (reesClosedCoefficientAdicCechIso J H I n d q).hom =
    (reesClosedCoefficientAdicCechIso J G I n d q).hom ≫
      reesClosedCoefficientAdicModuleCechMap I J f G H hf n d q := by
  convert reesCoefficientAdicCechIso_module_naturality
    (R := R) (B := R ⧸ J) (ι := ι) I
    (reesClosedCoefficientPiece (ι := ι) J G) (reesClosedCoefficientPiece (ι := ι) J H)
    (reesClosedCoefficientModuleMap J f)
    (reesClosedCoefficientModuleMap_preservesPiece J f G H hf) n d q using 1 <;> rfl

/-- 実際の閉厚化の I 進互換族の係数比較は、任意の元の次数付き加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedCoefficientAdicCechFamiliesEquiv_module_naturality
    (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q) :
    reesClosedCoefficientAdicCechFamiliesEquiv J H I d q
        (reesAdicProjectiveClosedCechModuleFamiliesMap I
          (reesAdicProjectiveQuotientPiece (ι := ι) J G 1)
          (reesAdicProjectiveQuotientPiece (ι := ι) J H 1)
          (reesAdicProjectiveQuotientMap J f 1)
          (reesAdicProjectiveQuotientMap_preservesPiece J f G H hf 1) d q x) =
      reesClosedCoefficientAdicModuleFamiliesMap I J f G H hf d q
        (reesClosedCoefficientAdicCechFamiliesEquiv J G I d q x) := by
  apply Subtype.ext
  funext n
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (reesClosedCoefficientAdicCechIso_module_naturality I J f G H hf n d q)) (x.val n)


variable [IsNoetherianRing R]
variable [Module.Finite (MvPolynomial ι R) M] [Module.Finite (MvPolynomial ι R) N]
local instance closedAdicModuleNatSourceFinite : Module.Finite (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  inferInstanceAs (Module.Finite (MvPolynomial ι R)
    (M ⧸ ((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
      (⊤ : Submodule (MvPolynomial ι R) M))))
local instance closedAdicModuleNatTargetFinite : Module.Finite (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) J 1) :=
  inferInstanceAs (Module.Finite (MvPolynomial ι R)
    (N ⧸ ((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
      (⊤ : Submodule (MvPolynomial ι R) N))))

/-- M/JM の商係数表示の Čech 形式関数は、任意の元の次数付き加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数の自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedCoefficientAdicCechFormalFunctions_module_naturality
    (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι)
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q)) :
    reesClosedCoefficientAdicModuleFamiliesMap I J f G H hf d q
        (reesClosedCoefficientAdicCechFormalFunctions J G I d q a) =
      reesClosedCoefficientAdicCechFormalFunctions J H I d q
        (AdicCompletion.map I (reesAdicProjectiveClosedCechModuleMap J G H f hf 1 d q).hom a) := by
  convert reesCoefficientAdicFormalFunctions_module_naturality
    (R := R) (B := R ⧸ J) (ι := ι) I
    (reesClosedCoefficientPiece (ι := ι) J G) (reesClosedCoefficientPiece (ι := ι) J H)
    (reesClosedCoefficientModuleMap J f)
    (reesClosedCoefficientModuleMap_preservesPiece J f G H hf) d q a using 1 <;> rfl

end SerrePositivity.AlgebraicGeometry
