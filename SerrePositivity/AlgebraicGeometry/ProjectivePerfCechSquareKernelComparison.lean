module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareComplexData
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareMaps

/-!
概要：F7 の H⁰ の差写像を F8 の実際の差の余鎖写像と零次項で照合する。
方針：H⁰・核の自然性と中心の増大写像の比較を合成する。
規約：固定した projectivePerfCechH0Difference の定義は変更しない。
使われ方：F7 の短完全性を増大全複体の零次項の完全性へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechSquareKernelComparisonGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- H⁰ の差写像を零次コサイクルへ移すと、実際の差の余鎖写像となる。 -/
theorem projectivePerfCechH0Difference_kernel
    (b : projectivePerfCechH0 (ι := ι) G p hp hR hA)
    (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    ((fullCechH0KernelIso (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))).hom.hom
        (projectivePerfCechH0Difference (ι := ι) G I p hp hR hA (b, c))).val =
    ((projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA).f 0).hom
      (((fullCechH0KernelIso
        (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).hom.hom b).val, c) := by
  let E := projectiveFrobeniusRingChartDiagram (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))
  let K := (fullCechH0KernelIso E).hom.hom
  let f := reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1
  have hn := congrArg (fun g ↦ g.hom b)
    (fullCechH0KernelIso_naturality_subtype
      (reesClosedFrobeniusRingChartMap (ι := ι) I G p hp hR hA 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hn
  have hc := projectivePerfCechH0CenterClass_augmentation (ι := ι) G I p hp hR hA c
  rw [projectivePerfCechH0Difference_apply]
  calc
    _ = (K ((HomologicalComplex.homologyMap f 0).hom b)).val -
        (K (projectivePerfCechH0CenterClass (ι := ι) G I p hp hR hA c)).val :=
      congrArg (fun z ↦ z.val) (map_sub K _ _)
    _ = fullCechCochainsMap
        (reesClosedFrobeniusRingChartMap (ι := ι) I G p hp hR hA 1) 1
        (((fullCechH0KernelIso
          (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).hom.hom b).val) -
        projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA c :=
      congrArg₂ (fun (x y : FullCechCochains E 1) ↦ x - y) hn hc
    _ = _ := rfl

end SerrePositivity.AlgebraicGeometry
