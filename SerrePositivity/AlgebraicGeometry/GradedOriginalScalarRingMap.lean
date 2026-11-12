module

public import SerrePositivity.AlgebraicGeometry.GradedScalarComponents
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousRingChartMap

/-!
概要：異なる carrier の次数付き環の射を、共通基底の部分加群の次数へ移す。
方針：環の射をそのまま使い、次数への所属だけを正規化する。
規約：元の Proj の射との比較では、元の grading の斉次局所化へ戻す。
使われ方：動く基底の標準開の filtered colimit の遷移の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory HomogeneousLocalization
universe u v w
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A]
variable {σ : Type v} {τ : Type w}
variable [SetLike σ S] [AddSubgroupClass σ S] [SMulMemClass σ R S]
variable [SetLike τ A] [AddSubgroupClass τ A] [SMulMemClass τ R A]
variable (G : ℕ → σ) (H : ℕ → τ) [GradedRing G] [GradedRing H]
variable (f : G →+*ᵍ H)

/-- 異なる carrier の次数付き環の射を、共通の基底環の部分加群の次数の射に移す。 -/
def gradedOriginalScalarRingMap :
    gradedScalarComponents (R := R) G →+*ᵍ gradedScalarComponents (R := R) H where
  toRingHom := f.toRingHom
  map_mem := fun h ↦ f.2 h

/-- 共通基底への正規化と、実際の斉次局所化の射は可換。 -/
theorem gradedScalarAwayIso_map {s : S} {t : A}
    (hmap : Submonoid.powers s ≤ (Submonoid.powers t).comap f.toRingHom)
    (z : Away (gradedScalarComponents (R := R) G) s) :
    (gradedScalarAwayIso (R := R) H t).hom.hom
        (HomogeneousLocalization.map (gradedOriginalScalarRingMap (R := R) G H f) hmap z) =
      HomogeneousLocalization.map f hmap ((gradedScalarAwayIso (R := R) G s).hom.hom z) := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rfl

variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]
variable [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (g : S →ₐ[MvPolynomial ι R] A) (hfg : ∀ x, f x = g x)

include hfg in
/-- 元の grading の射は、標準開の分母を同じ変数の像の積へ送る。 -/
theorem gradedOriginalScalarRingMap_denominator (T : Finset ι) :
    f (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) =
      algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T) := by
  rw [hfg, g.commutes]

include hfg in
/-- 元の grading の射で標準開の分母の冪を移す包含。 -/
theorem gradedOriginalScalarRingMap_powers (T : Finset ι) :
    Submonoid.powers (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) ≤
      (Submonoid.powers (algebraMap (MvPolynomial ι R) A
        (projectiveLaurentDenominator R T))).comap f.toRingHom := by
  rintro _ ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  change _ = f (_ ^ n)
  rw [map_pow, gradedOriginalScalarRingMap_denominator G H f g hfg T]

/-- 共通基底の加群でのチャートの射を、元の grading の斉次局所化の射へ戻す。 -/
theorem gradedOriginalChartLinearEquiv_map (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι)
      (gradedScalarComponents (R := R) G) 0).obj T) :
    (gradedScalarAwayIso (R := R) H _).hom.hom
      (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) H) T
        (((projectiveNatGradedModuleChartMap (gradedScalarComponents (R := R) G)
          (gradedScalarComponents (R := R) H) g.toLinearMap
          (fun n m hm ↦ by change g m ∈ H n; rw [← hfg]; exact f.2 hm) 0).app T).hom z)) =
    HomogeneousLocalization.map f (gradedOriginalScalarRingMap_powers G H f g hfg T)
      ((gradedScalarAwayIso (R := R) G _).hom.hom
        (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G) T z)) := by
  rw [projectiveHomogeneousChartLinearEquiv_map (gradedScalarComponents (R := R) G)
    (gradedScalarComponents (R := R) H) (gradedOriginalScalarRingMap (R := R) G H f)
    g hfg T z]
  exact gradedScalarAwayIso_map (R := R) G H f _ _

end SerrePositivity.AlgebraicGeometry
