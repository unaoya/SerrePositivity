module

public import SerrePositivity.AlgebraicGeometry.SchemeCechSectionSpectrum
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSectionAlgebra
public import SerrePositivity.AlgebraicGeometry.FrobeniusFiniteModificationSquare

/-!
概要：射影標準開の有限切断環へ、元の構造射の全射性を移す。
方針：標準開の被覆条件を大域切断の比較へ入れ、Spec 全射性から Frobenius 順極限の単射性を得る。
規約：中心外の同型や正次数の消滅はこの単射性には不要。
使われ方：F7 の短完全列の左端を、幾何学的な仮定から供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))))
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

include hspan in
/-- 全射な射影構造射の Čech 切断環は、基底の Spec に全射する。 -/
theorem projectiveCechSectionAlgebra_surjectiveSpectrum :
    Function.Surjective (PrimeSpectrum.comap
      (algebraMap R (projectiveCechSectionAlgebra (ι := ι) G))) :=
  schemeCechSectionAlgebra_surjectiveSpectrum (Proj G) (projectiveProjCechOpen (ι := ι) G)
    (projectiveScalarToGlobalSections G) (Proj.iSup_basicOpen_eq_top G _ hspan)

/-- 基底環で p が零なら、Čech 切断環でも p は零。 -/
theorem projectiveCechSectionAlgebra_primeCast (p : ℕ) (hR : (p : R) = 0) :
    (p : projectiveCechSectionAlgebra (ι := ι) G) = 0 := by
  simpa using congrArg (algebraMap R (projectiveCechSectionAlgebra (ι := ι) G)) hR

include hspan in
/-- 全射な射影構造射は、Čech 切断環の Frobenius 順極限への単射を与える。 -/
theorem projectiveCechSectionAlgebra_frobenius_injective
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    Function.Injective (frobeniusDirectLimitMap p hp hR
      (projectiveCechSectionAlgebra_primeCast (ι := ι) G p hR)
      (algebraMap R (projectiveCechSectionAlgebra (ι := ι) G))) :=
  frobeniusDirectLimitMap_injective_of_surjectiveSpectrum p hp hR _ _
    (projectiveCechSectionAlgebra_surjectiveSpectrum G hspan)

end SerrePositivity.AlgebraicGeometry
