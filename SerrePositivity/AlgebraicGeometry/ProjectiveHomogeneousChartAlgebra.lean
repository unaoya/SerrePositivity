module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartRestriction
public import SerrePositivity.AlgebraicGeometry.CechAlgebraH0Naturality

/-!
概要：標準開の斉次局所化の係数図式に、元の環の積を保つ代数構造を与える。
方針：既存の加群構造と局所化への単射でスカラーと積を照合する。
規約：加群図式を忘却したときに既存の線形写像をそのまま使う。
使われ方：閉厚化への環の射を適合切断代数の射として扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G]

/-- 既存の斉次局所化の加群構造と整合する、基底環上の代数構造。 -/
@[instance_reducible]
def projectiveHomogeneousAwayAlgebra (f : A) :
    Algebra R (HomogeneousLocalization.Away G f) := by
  letI := projectiveHomogeneousAwayModule G f
  apply Algebra.ofModule
  · intro r x y
    apply HomogeneousLocalization.val_injective (Submonoid.powers f)
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_smul,
      smul_mul_assoc]
  · intro r x y
    apply HomogeneousLocalization.val_injective (Submonoid.powers f)
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_smul,
      mul_smul_comm]

local instance homogeneousChartAlgebraBase (f : A) : Algebra R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayAlgebra G f

variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 標準開の制限を、既存の線形写像と同じ基底環上の代数写像にする。 -/
def projectiveHomogeneousChartRestrictionAlgHom {T U : Finset ι} (h : T ⊆ U) :
    HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)) →ₐ[R]
    HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R U)) :=
  AlgHom.ofLinearMap ((projectiveHomogeneousChartDiagram (ι := ι) G).map (homOfLE h)).hom
    (by exact (projectiveHomogeneousChartDiagram_map G h
      (1 : HomogeneousLocalization.Away G
        (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))).trans (map_one (projectiveHomogeneousChartRestrictionRingHom G h)))
    (by
      intro x y
      exact (projectiveHomogeneousChartDiagram_map G h (x * y)).trans
        ((map_mul (projectiveHomogeneousChartRestrictionRingHom G h) x y).trans
          (congrArg₂ (fun (x y : HomogeneousLocalization.Away G
            (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R U))) ↦ x * y)
          (projectiveHomogeneousChartDiagram_map G h x).symm
          (projectiveHomogeneousChartDiagram_map G h y).symm)))

/-- 標準開の斉次局所化の代数係数図式。 -/
def projectiveHomogeneousChartAlgebraDiagram : Finset ι ⥤ CommAlgCat.{u} R where
  obj T := CommAlgCat.of R (HomogeneousLocalization.Away G
    (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))
  map h := CommAlgCat.ofHom (projectiveHomogeneousChartRestrictionAlgHom G (leOfHom h))
  map_id T := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun f ↦ f.hom x) ((projectiveHomogeneousChartDiagram (ι := ι) G).map_id T)
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun f ↦ f.hom x)
      ((projectiveHomogeneousChartDiagram (ι := ι) G).map_comp f g)

/-- 代数図式の忘却は、既存の斉次局所化の加群図式に一致する。 -/
theorem projectiveHomogeneousChartAlgebraDiagram_forget :
    algebraCechModuleDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) =
      projectiveHomogeneousChartDiagram (ι := ι) G := rfl

end SerrePositivity.AlgebraicGeometry
