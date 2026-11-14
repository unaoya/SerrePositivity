module

public import SerrePositivity.AlgebraicGeometry.PolynomialProjProper
public import SerrePositivity.AlgebraicGeometry.HomogeneousPolynomialChartEvaluation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
概要：多項式 affine を、Proj の一標準開を通じて実際に immersion する。
方針：標準開の次数零局所化からの全射と開包含を合成し、係数上の可換式を追う。
規約：元の係数環の Noether 性は要求しない。
使われ方：C05 の有限型 affine の固有な周辺への immersion。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) (ι : Type u) [CommRing R]

/-- 標準開の次数零局所化の評価を Spec に移した、実際の Proj への射。 -/
def polynomialAffineToProj : Spec (CommRingCat.of (MvPolynomial ι R)) ⟶
    Proj (MvPolynomial.homogeneousSubmodule (Option ι) R) :=
  Spec.map (CommRingCat.ofHom (homogeneousPolynomialChartEvaluation R ι)) ≫
    Proj.awayι _ (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X R none) (by decide)

/-- 多項式 affine の指定した Proj への射は immersion。 -/
theorem isImmersion_polynomialAffineToProj : IsImmersion (polynomialAffineToProj R ι) := by
  haveI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (homogeneousPolynomialChartEvaluation R ι))) :=
    IsClosedImmersion.spec_of_surjective _ (homogeneousPolynomialChartEvaluation_surjective R ι)
  dsimp [polynomialAffineToProj]
  infer_instance

/-- 指定した immersion と Proj の構造射の合成は、元の係数射の Spec。 -/
theorem polynomialAffineToProj_toSpec :
    polynomialAffineToProj R ι ≫ polynomialProjToSpec R (Option ι) =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))) := by
  let G := MvPolynomial.homogeneousSubmodule (Option ι) R
  let z := HomogeneousLocalization.fromZeroRingHom G (.powers (MvPolynomial.X none))
  let χ := CommRingCat.ofHom (homogeneousPolynomialChartEvaluation R ι)
  have hc : CommRingCat.ofHom (polynomialGradeZeroMap R (Option ι)) ≫
      CommRingCat.ofHom z ≫ χ =
        CommRingCat.ofHom (algebraMap R (MvPolynomial ι R)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact homogeneousPolynomialChartEvaluation_fromZero R ι r
  calc
    _ = Spec.map χ ≫ (Proj.awayι G (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X R none)
        (by decide) ≫ Proj.toSpecZero G) ≫
          Spec.map (CommRingCat.ofHom (polynomialGradeZeroMap R (Option ι))) := by
      simp only [polynomialAffineToProj, polynomialProjToSpec, χ, G, Category.assoc]
    _ = Spec.map χ ≫ Spec.map (CommRingCat.ofHom z) ≫
        Spec.map (CommRingCat.ofHom (polynomialGradeZeroMap R (Option ι))) := by
      rw [Proj.awayι_toSpecZero]
    _ = _ := by rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc, hc]

end SerrePositivity.AlgebraicGeometry
