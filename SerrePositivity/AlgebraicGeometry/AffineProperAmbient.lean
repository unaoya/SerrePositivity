module

public import SerrePositivity.AlgebraicGeometry.AffinePolynomialClosedEmbedding
public import SerrePositivity.AlgebraicGeometry.PolynomialAffineProjImmersion

/-!
概要：任意の有限型 affine に、元の係数環上の固有な周辺への実際の immersion を供給する。
方針：多項式空間への閉埋め込みと、標準開を通る Proj への immersion を合成する。
規約：Stacks 01VS の affine の場合の帰結。係数環の Noether 性は要求しない。
使われ方：C06 の Chow の補題の有限 affine 被覆の周辺空間。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 有限型 affine は、元の係数環上の固有なスキームへ実際に immersion する。 -/
theorem exists_affine_immersion_proper_ambient
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    ∃ (P : Scheme.{u}) (q : P ⟶ Spec (CommRingCat.of R))
      (j : Spec (CommRingCat.of A) ⟶ P),
      IsProper q ∧ IsImmersion j ∧
        j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  classical
  obtain ⟨s, j, hj, hcomm⟩ := exists_affine_polynomial_closed_embedding R A
  letI : IsClosedImmersion j := hj
  haveI : IsImmersion (polynomialAffineToProj R s) := isImmersion_polynomialAffineToProj R s
  refine ⟨_, polynomialProjToSpec R (Option s), j ≫ polynomialAffineToProj R s,
    isProper_polynomialProjToSpec R (Option s), inferInstance, ?_⟩
  rw [Category.assoc, polynomialAffineToProj_toSpec]
  exact hcomm

end SerrePositivity.AlgebraicGeometry
