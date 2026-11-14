module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSectionComparison
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFiniteCenterExact
public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionFrobeniusComparison

/-!
概要：斉次標準開の切断代数の有限変更の四角形を幾何学的な仮定から作る。
方針：構造層の切断代数との代数同型で Spec と局所化の全射性を移す。
規約：右下は切断代数の商。閉厚化の切断への比較は別の写像。
使われ方：F7 の閉厚化の Frobenius 比較と合成する有限環側。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))

include hspan in
/-- 全射な射影構造射の斉次切断代数は、基底の Spec に全射する。 -/
theorem projectiveHomogeneousSectionAlgebra_surjectiveSpectrum
    [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))] :
    Function.Surjective (PrimeSpectrum.comap
      (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G))) := by
  intro P
  obtain ⟨Q, hQ⟩ := projectiveCechSectionAlgebra_surjectiveSpectrum G hspan P
  let e := projectiveCechSectionAlgebraEquiv (ι := ι) G
  refine ⟨PrimeSpectrum.comap e.toRingHom Q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  have he : e.toRingHom.comp (algebraMap R _) = algebraMap R _ := by
    apply RingHom.ext
    intro r
    exact e.commutes r
  rw [he]
  exact hQ

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (I : Ideal R)
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]

include hspan in
/-- 中心外では、基底から斉次切断代数への局所化した写像は全射。 -/
theorem projectiveHomogeneousSectionAlgebra_localized_surjective
    (P : PrimeSpectrum R) (hP : P ∉ PrimeSpectrum.zeroLocus (I : Set R)) :
    Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl
      (Algebra.linearMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G))) := by
  let e := projectiveCechSectionAlgebraEquiv (ι := ι) G
  let S := P.asIdeal.primeCompl
  let le := LocalizedModule.map S e.toLinearMap
  have hi : Function.Injective le := LocalizedModule.map_injective S _ e.injective
  intro x
  obtain ⟨r, hr⟩ := projectiveCechSectionAlgebra_localized_surjective G hspan I P hP (le x)
  refine ⟨r, hi ?_⟩
  have hc : ∀ r : LocalizedModule S R,
      le (LocalizedModule.map S (Algebra.linearMap R
        (projectiveHomogeneousSectionAlgebra (ι := ι) G)) r) =
      LocalizedModule.map S (Algebra.linearMap R
        (projectiveCechSectionAlgebra (ι := ι) G)) r := by
    intro r
    induction r using LocalizedModule.induction_on with
    | _ a s =>
      change LocalizedModule.map S e.toLinearMap _ = _
      simp only [LocalizedModule.map_mk]
      exact congrArg (fun a ↦ LocalizedModule.mk a s) (e.commutes a)
  exact (hc r).trans hr

include hspan in
/-- 斉次切断代数の有限変更の四角形は Frobenius 順極限で短完全。
閉厚化の切断代数への比較前の、商 B/IB を右下とする主張。 -/
theorem projectiveHomogeneousFiniteCenter_exact
    [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    let hB := projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR
    let f := algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)
    Function.Injective (frobeniusCenterPair p hp hR hB f I) ∧
    Function.Exact (frobeniusCenterPair p hp hR hB f I)
      (frobeniusCenterDifference p hp hR hB f I) ∧
    Function.Surjective (frobeniusCenterDifference p hp hR hB f I) := by
  letI := projectiveHomogeneousSectionAlgebra_finite (ι := ι) G
  exact frobeniusFiniteModification_exact p hp hR _ I
    (projectiveHomogeneousSectionAlgebra_surjectiveSpectrum G hspan)
    (Ideal.fg_of_isNoetherianRing I)
    (projectiveHomogeneousSectionAlgebra_localized_surjective G hspan I)

end SerrePositivity.AlgebraicGeometry
