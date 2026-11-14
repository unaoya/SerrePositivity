module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechScalarAugmentation
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitModuleIso
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjCechComplexIso
public import SerrePositivity.AlgebraicGeometry.OpenCoverFrobeniusRefinement

/-!
概要：F8 の実際の斉次局所化の Frobenius 係数を、Proj の実際の構造層へ移す。
方針：非空交叉の環の同型とその自然性を Frobenius 順極限へ送り、全タプル複体にする。
規約：空交叉の斉次局所化と大域切断を同一視しない。
使われ方：共通アフィン比較を F8 の固定した標準開の複体に接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 標準開の切断環の比較は、基底環の実際のスカラーと整合する。 -/
theorem projectiveProjCechSectionRingIso_scalar (T : Finset ι) (hT : T.Nonempty) (r : R) :
    (projectiveProjCechSectionRingIso G T hT).hom.hom
        (algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj T) r) =
      ((Proj G).presheaf.map (homOfLE (show
        cechOpenIntersection (projectiveProjCechOpen G) T ≤ ⊤ from le_top)).op).hom
        (projectiveScalarToGlobalSections G r) := by
  have h := (projectiveProjCechSectionLinearEquiv G T hT).map_smul r
    (1 : HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))
  change (projectiveProjCechSectionRingIso G T hT).hom.hom (r • 1) =
    ((Proj G).presheaf.map (homOfLE (show
      cechOpenIntersection (projectiveProjCechOpen G) T ≤ ⊤ from le_top)).op).hom
        (projectiveScalarToGlobalSections G r) *
        (projectiveProjCechSectionRingIso G T hT).hom.hom 1 at h
  rw [map_one, mul_one] at h
  convert h using 1
  congr 1

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- native な零次コチェインの増大写像は、基底の実際のスカラーの Frobenius 順極限。 -/
theorem projectivePerfectNativeCechComplexIso_scalar
    (a : FrobeniusDirectLimit R p hp hR) (t : Fin 1 → ι) :
    (((projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA).hom.f 0).hom
      (projectivePerfCechScalarAugmentation (ι := ι) G p hp hR hA a)) t =
      frobeniusDirectLimitMap p hp hR
        (projectiveProjPresheaf_primeCast G p hR _)
        (((Proj G).presheaf.map (homOfLE (show
          cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t) ≤ ⊤ from le_top)).op).hom.comp
          (projectiveScalarToGlobalSections G)) a := by
  rw [projectivePerfectNativeCechComplexIso_apply]
  obtain ⟨k, r, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap R p hp hR) a
  change frobeniusDirectLimitOf _ p hp _ k
    ((projectiveProjCechSectionRingIso G (cechTupleSupport t) (cechTupleSupport_nonempty t)).hom.hom
      (algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj (cechTupleSupport t)) r)) =
    frobeniusDirectLimitOf _ p hp _ k _
  exact congrArg (frobeniusDirectLimitOf _ p hp _ k)
    (projectiveProjCechSectionRingIso_scalar G (cechTupleSupport t) (cechTupleSupport_nonempty t) r)

end SerrePositivity.AlgebraicGeometry
