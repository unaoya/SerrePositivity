module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectCartesianSquare
public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeCenterAugmentation
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareTransport
public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeProjection

/-!
概要：F8 の増大全複体を、実際の Cartesian な閉厚化の構造層へ移す。
方針：二つの Čech 複体の検証済みの同型を四角形ごと移し、全複体の同型を使う。
規約：完全性を仮定に追加せず、F8 の既存の acyclicity から証明する。
使われ方：native な被覆比較と F8 の全複体の接続。
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
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfectCartesianEdgesGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G 1
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1)))
variable (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))))

/-- 実際の閉厚化の構造射のスカラーで定める、中心の零次コチェインへの増大写像。 -/
def projectivePerfectCartesianCenterAugmentation :
    FrobeniusDirectLimit (R ⧸ I ^ 1) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1)) →ₗ[ℤ]
      (fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
        (fun i ↦ g ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i))).X 0 :=
  ((schemeCechPreimageComplexIso g
    (frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
    (projectiveProjCechOpen (ι := ι) G)).hom.f 0).hom.comp
      (LinearMap.pi fun t ↦ (frobeniusDirectLimitMap p hp
        (frobeniusQuotientPrimeCast p hR (I ^ 1))
        (projectivePullbackPresheaf_primeCast G g p hR _)
        ((Y.presheaf.map (homOfLE (show
          g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t) ≤ ⊤
            from le_top)).op).hom.comp (schemeScalarHom Y iY))).toAddMonoidHom.toIntLinearMap)

/-- 四角形の中心側の辺は、実際の構造射から作った増大写像と同じ。 -/
theorem projectivePerfectCartesianAugmentedSquare_center :
    (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).center =
      projectivePerfectCartesianCenterAugmentation G I p hp hR iY g := by
  dsimp only [projectivePerfectCartesianAugmentedSquare, CechAugmentedSquare.transport,
    projectivePerfectCartesianCenterAugmentation, reesClosedPerfectNativeCechIso,
    Iso.trans_hom, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  rw [LinearMap.comp_assoc]
  congr 1
  apply LinearMap.ext
  intro a
  funext t
  exact reesClosedPerfectNativePushedCechIso_center I G iY g H p hp hR hA a t

/-- 四角形の基底側のスカラーは、実際の大域スカラーを制限した Frobenius の写像。 -/
theorem projectivePerfectCartesianAugmentedSquare_scalar_apply
    (a : FrobeniusDirectLimit R p hp hR) (t : Fin 1 → ι) :
    (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).scalar a t =
      frobeniusDirectLimitMap p hp hR (projectiveProjPresheaf_primeCast G p hR _)
        (((Proj G).presheaf.map (homOfLE (show
          cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t) ≤ ⊤
            from le_top)).op).hom.comp (projectiveScalarToGlobalSections G)) a :=
  projectivePerfectNativeCechComplexIso_scalar G p hp hR hA a t

end SerrePositivity.AlgebraicGeometry
