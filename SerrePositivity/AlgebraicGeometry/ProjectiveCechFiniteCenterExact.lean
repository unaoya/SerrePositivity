module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSectionSpectrum
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechScalarConductor
public import SerrePositivity.AlgebraicGeometry.FrobeniusFiniteModificationExact

/-!
概要：射影スキームの有限切断環と基底の中心が作る Frobenius 四角形の短完全性。
方針：Spec 全射性、射影有限性、中心外の余核の台の消滅を有限変更の定理へ渡す。
規約：右下は切断環の商であり、閉厚化の切断環との比較は別途必要。
使われ方：F7 の次数零の四角形を閉厚化の切断環へ移す前の有限環側。
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
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) S]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))))
variable (I : Ideal R)
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]

include hspan in
/-- 中心外では、基底から射影 Čech 切断環への写像の局所化は全射。 -/
theorem projectiveCechSectionAlgebra_localized_surjective
    (P : PrimeSpectrum R) (hP : P ∉ PrimeSpectrum.zeroLocus (I : Set R)) :
    Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl
      (Algebra.linearMap R (projectiveCechSectionAlgebra (ι := ι) G))) := by
  apply (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ _).mpr
  apply Module.notMem_support_iff.mp
  intro h
  exact hP (projectiveCechScalarCokernel_support G hspan I h)

include hspan in
/-- 射影構造射の有限切断環による中心の四角形は Frobenius 順極限で短完全。
右下の環は B/IB であり、閉厚化の Čech H⁰ への比較をこの主張に含めない。 -/
theorem projectiveCechFiniteCenter_exact
    [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    let hB := projectiveCechSectionAlgebra_primeCast (ι := ι) G p hR
    let f := algebraMap R (projectiveCechSectionAlgebra (ι := ι) G)
    Function.Injective (frobeniusCenterPair p hp hR hB f I) ∧
    Function.Exact (frobeniusCenterPair p hp hR hB f I)
      (frobeniusCenterDifference p hp hR hB f I) ∧
    Function.Surjective (frobeniusCenterDifference p hp hR hB f I) := by
  letI := projectiveCechSectionAlgebra_finite (ι := ι) G
  exact frobeniusFiniteModification_exact p hp hR _ I
    (projectiveCechSectionAlgebra_surjectiveSpectrum G hspan)
    (Ideal.fg_of_isNoetherianRing I)
    (projectiveCechSectionAlgebra_localized_surjective G hspan I)

end SerrePositivity.AlgebraicGeometry
