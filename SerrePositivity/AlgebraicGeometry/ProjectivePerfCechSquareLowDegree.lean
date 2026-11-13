module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareAugmentationComparison
public import SerrePositivity.AlgebraicGeometry.AugmentedCechCone

/-!
概要：F7 の短完全列を、F8 の実際の増大全複体の低次数の完全性へ移す。
方針：H⁰ と零次コサイクルの同型を使い、元の完全列で持ち上げる。
規約：単なる条件付きの全複体の完全性を完成とは呼ばず、F7 の結論を供給する。
使われ方：実際のブローアップ四角形の全複体の最初の完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u v
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechSquareLowDegreeGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

include hspan in
/-- 実際の差の余鎖写像と基底の増大写像の合成は零。 -/
theorem projectivePerfCechSquareDifference_augmentation_zero
    (a : FrobeniusDirectLimit R p hp hR) :
    ((projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA).f 0).hom
      (projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA a) = 0 := by
  have he := (projectivePerfCechH0_square_exact (ι := ι) G I p hp hR hA hspan).2.1
  have hz := (he (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA a)).mpr ⟨a, rfl⟩
  rw [← projectivePerfCechH0Pair_cochains]
  have hk := projectivePerfCechH0Difference_kernel (ι := ι) G I p hp hR hA
    (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA a).1
    (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA a).2
  refine hk.symm.trans ?_
  change ((fullCechH0KernelIso (projectiveFrobeniusRingChartDiagram (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))).hom.hom
      (projectivePerfCechH0Difference (ι := ι) G I p hp hR hA
        (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA a))).val = 0
  rw [hz, map_zero]
  rfl

include hspan in
/-- F7 の短完全性を実際の増大写像と cone の最初の微分の完全性へ移す。 -/
theorem projectivePerfCechSquareAugmentation_exact :
    Function.Exact (projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA)
      (cechRefinementConeDifferential
        (projectivePerfCechSquareSource (ι := ι) G I p hp hR hA)
        (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
          (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
          (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))))
        (projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA) 0) := by
  let E := projectiveFrobeniusRingChartDiagram (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))
  let K := (fullCechH0KernelIso E).hom.hom
  let g := projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA
  have he := (projectivePerfCechH0_square_exact (ι := ι) G I p hp hR hA hspan).2.1
  intro x
  constructor
  · intro hx
    change ((g.f 0).hom x,
      -((projectivePerfCechSquareSource (ι := ι) G I p hp hR hA).d 0 1).hom x) = (0, 0) at hx
    have hg : (g.f 0).hom x = 0 := congrArg Prod.fst hx
    have hc : ((projectivePerfCechSquareSource (ι := ι) G I p hp hR hA).d 0 1).hom x = 0 :=
      neg_eq_zero.mp (congrArg Prod.snd hx)
    obtain ⟨b, hb⟩ := fullCechH0ZeroTermCochainMap_surjective_cycles
      (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)
      (ModuleCat.of ℤ (FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
        (frobeniusQuotientPrimeCast p hR (I ^ 1)))) x hc
    have hb' : projectivePerfCechH0ToSquareCochains (ι := ι) G I p hp hR hA b = x := hb
    have hk := projectivePerfCechH0Difference_kernel (ι := ι) G I p hp hR hA b.1 b.2
    have hv : (K (projectivePerfCechH0Difference (ι := ι) G I p hp hR hA b)).val = 0 :=
      hk.trans ((congrArg (fun z ↦ (g.f 0).hom z) hb').trans hg)
    have hz : projectivePerfCechH0Difference (ι := ι) G I p hp hR hA b = 0 := by
      apply (fullCechH0KernelIso E).toLinearEquiv.injective
      exact (Subtype.ext hv).trans (map_zero K).symm
    obtain ⟨a, ha⟩ := (he b).mp hz
    exact ⟨a, (projectivePerfCechH0Pair_cochains (ι := ι) G I p hp hR hA a).symm.trans
      ((congrArg (projectivePerfCechH0ToSquareCochains (ι := ι) G I p hp hR hA) ha).trans hb')⟩
  · rintro ⟨a, rfl⟩
    change ((g.f 0).hom (projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA a),
      -((projectivePerfCechSquareSource (ι := ι) G I p hp hR hA).d 0 1).hom
        (projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA a)) = (0, 0)
    rw [projectivePerfCechSquareDifference_augmentation_zero (ι := ι) G I p hp hR hA hspan,
      projectivePerfCechSquareAugmentation_cycle, neg_zero]

end SerrePositivity.AlgebraicGeometry
