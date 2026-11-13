module

public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeCenter
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechCenterAugmentation
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeScalar
public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectChartMap
public import SerrePositivity.AlgebraicGeometry.FullCechComplexHomExt
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitModuleIsoNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback

/-!
概要：実際の Cartesian な閉厚化への制限と、Frobenius 係数の比較の自然性。
方針：非空交叉の環の同型を順極限へ送り、逆像と交叉の比較を合成する。
規約：次数付き商の Proj と pullback のスキームの同一視は使わない。
使われ方：F8 の閉厚化の複体を canonical な実際の基底変更へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local notation "n" => (1 : ℕ)
local instance closedPerfectNativeCenterAugGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- 中心の環の写像は、実際の閉厚化の構造射から得るスカラーに対応する。 -/
theorem reesClosedNativeSectionRingIso_center (t : Fin 1 → ι) (z : R ⧸ I ^ 1) :
    (reesClosedNativeSectionRingIso I G 1 iY g H
      (cechTupleSupport t) (cechTupleSupport_nonempty t)).hom.hom
        (projectiveClosedCenterChartMap (ι := ι) G I t z) =
      (Y.presheaf.map (homOfLE (show
        g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t) ≤ ⊤
          from le_top)).op).hom (schemeScalarHom Y iY z) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [projectiveClosedCenterChartMap_mk, reesClosedNativeSectionRingIso_scalar]
  have h := schemeScalarHom_naturality (Proj G) g
    (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
    iY (Ideal.Quotient.mk (I ^ 1)) H.w
  rw [schemeScalarHom_scalarMorphism] at h
  exact congrArg (fun z ↦ (Y.presheaf.map (homOfLE (show
    g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t) ≤ ⊤
      from le_top)).op).hom z) (congrArg (fun f : R →+* Γ(Y, ⊤) ↦ f r) h).symm

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 実際の中心の増大写像は、構造射のスカラーの Frobenius 順極限。 -/
theorem reesClosedPerfectNativePushedCechIso_center
    (a : FrobeniusDirectLimit (R ⧸ I ^ 1) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1)))
    (t : Fin 1 → ι) :
    (((reesClosedPerfectNativePushedCechIso I G 1 iY g H p hp hR hA).hom.f 0).hom
      (projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA a)) t =
      frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))
        (projectivePullbackPresheaf_primeCast G g p hR _)
        ((Y.presheaf.map (homOfLE (show
          g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t) ≤ ⊤
            from le_top)).op).hom.comp (schemeScalarHom Y iY)) a := by
  rw [reesClosedPerfectNativePushedCechIso_apply]
  obtain ⟨k, z, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (R ⧸ I ^ 1) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) a
  change frobeniusDirectLimitOf _ p hp _ k
    ((reesClosedNativeSectionRingIso I G 1 iY g H
      (cechTupleSupport t) (cechTupleSupport_nonempty t)).hom.hom
        (projectiveClosedCenterChartMap (ι := ι) G I t z)) =
    frobeniusDirectLimitOf _ p hp _ k _
  exact congrArg (frobeniusDirectLimitOf _ p hp _ k)
    (reesClosedNativeSectionRingIso_center I G iY g H t z)

end SerrePositivity.AlgebraicGeometry
