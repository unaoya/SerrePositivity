module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechThickeningFrobenius
public import SerrePositivity.AlgebraicGeometry.ReesClosedLocalizedThickeningFactor
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFrobenius

/-!
概要：閉厚化 Frobenius の因子分解を、捻り零の整数係数 Čech 図式で表す。
方針：局所化の因子分解を指定次数部分へ制限する。
規約：厚さ n→p^e*n の射を、元の厚さへ戻した反復 Frobenius と比較する。
使われ方：F6 の核の評価と像の安定化への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable [LinearOrder ι] [Fintype ι]
variable (I : Ideal R) (G : ℕ → Submodule R A) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedMonoid G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 閉厚化を経由する Frobenius の捻り零の整数線形な図式の射。 -/
def reesClosedCechIntThickeningDiagram (n e : ℕ) :
    projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) 0 ⋙
        ModuleCat.restrictScalars (Int.castRingHom R) ⟶
    projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G) 0 ⋙
        ModuleCat.restrictScalars (Int.castRingHom R) where
  app T := by
    let F := reesClosedChartThickeningFrobenius I G p hp hR hA n e T 0
    exact ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (Int.castRingHom R)).obj
        ((projectiveNatGradedModuleChartDiagram (ι := ι)
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) 0).obj T))
      (Y := (ModuleCat.restrictScalars (Int.castRingHom R)).obj
        ((projectiveNatGradedModuleChartDiagram (ι := ι)
          (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G) 0).obj T))
      { toFun := F
        map_add' := F.map_add
        map_smul' := by
          intro r z
          change F ((r : R) • z) = (r : R) • F z
          simp only [Int.cast_smul_eq_zsmul, map_zsmul] }
  naturality {T U} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact congrArg (fun f ↦ f.hom z)
      ((reesClosedChartThickeningFrobeniusNatTrans I G p hp hR hA n e 0).naturality h)

/-- 厚化から戻すと、同じ閉厚化の整数係数図式の反復 Frobenius になる。 -/
theorem reesClosedCechIntThickeningDiagram_factor (n e : ℕ) :
    reesClosedCechIntThickeningDiagram (ι := ι) I G p hp hR hA n e ≫
      Functor.whiskerRight
        (reesClosedRingTransitionChartMap (ι := ι) I G (p ^ e * n) n
          (Nat.le_mul_of_pos_left n (pow_pos hp.pos e)) 0)
        (ModuleCat.restrictScalars (Int.castRingHom R)) =
    projectiveCechIntFrobeniusDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) e := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact (reesClosedLocalizedThickeningFrobenius_factor I p hp hR hA
    (projectiveLaurentDenominator R T) n e z.val).trans
    (projectiveChartIteratedFrobenius_val
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) T e z).symm

/-- 射影後の厚化 Frobenius は、元の図式の反復 Frobenius 後の射影。 -/
theorem reesClosedCechIntThickeningDiagram_projection (n e : ℕ) :
    Functor.whiskerRight (reesClosedRingProjectionChartMap (ι := ι) I G n 0)
        (ModuleCat.restrictScalars (Int.castRingHom R)) ≫
      reesClosedCechIntThickeningDiagram (ι := ι) I G p hp hR hA n e =
    projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA e ≫
      Functor.whiskerRight (reesClosedRingProjectionChartMap (ι := ι) I G (p ^ e * n) 0)
        (ModuleCat.restrictScalars (Int.castRingHom R)) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  have hf := projectiveChartIteratedFrobenius_val G p hp hR hA T e z
  change reesClosedLocalizedThickeningFrobenius I p hp hR hA
    (projectiveLaurentDenominator R T) n e _ =
    IsLocalizedModule.map _ _ _ _ (projectiveChartIteratedFrobenius G p hp hR hA T e z).val
  rw [hf]
  exact reesClosedLocalizedThickeningFrobenius_projection I p hp hR hA
    (projectiveLaurentDenominator R T) n e z.val

end SerrePositivity.AlgebraicGeometry
