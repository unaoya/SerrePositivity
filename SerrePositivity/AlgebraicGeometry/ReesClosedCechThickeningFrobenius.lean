module

public import SerrePositivity.AlgebraicGeometry.ReesClosedChartThickeningFrobenius
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSemilinearMap

/-!
概要：閉厚化を経由する反復 Frobenius を、実際の標準開の Čech H へ送る。
方針：局所化の制限との可換性で係数図式の射を作り、既存の半線形 H の API を使う。
規約：厚さ n は p^e*n、捻り d は p^e*d へ移る。
使われ方：BST13 Lemma 3.9 の像の安定化と核の評価への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [DecidableEq ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)


/-- 既存の厚化 Frobenius 自然変換の成分を分離したもの。 -/
def reesClosedChartThickeningFrobeniusApp (n e : ℕ) (d : ℤ) (T : Finset ι) :
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d).obj T ⟶
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)
      (((p ^ e : ℕ) : ℤ) * d) ⋙ ModuleCat.restrictScalars (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))).obj T := by
  let F := reesClosedChartThickeningFrobenius I G p hp hR hA n e T d
  exact ModuleCat.ofHom
    (X := (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d).obj T)
    (Y := (ModuleCat.restrictScalars
      (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))).obj
      ((projectiveNatGradedModuleChartDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)
        (((p ^ e : ℕ) : ℤ) * d)).obj T))
    { toFun := fun z ↦ F z
      map_add' := F.map_add
      map_smul' r z := map_smulₛₗ F r z }

/-- 同じ成分の自然性。元の自然変換の証明を分離する。 -/
theorem reesClosedChartThickeningFrobeniusApp_naturality (n e : ℕ) (d : ℤ)
    {T U : Finset ι} (h : T ⟶ U) :
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d).map h ≫
        reesClosedChartThickeningFrobeniusApp I G p hp hR hA n e d U =
      reesClosedChartThickeningFrobeniusApp I G p hp hR hA n e d T ≫
        (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)
      (((p ^ e : ℕ) : ℤ) * d) ⋙ ModuleCat.restrictScalars (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))).map h := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change reesClosedLocalizedThickeningFrobenius I p hp hR hA
    (projectiveLaurentDenominator R U) n e
    (projectiveModuleAwayRestriction
      (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
        ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm⟩) z.val) =
    projectiveModuleAwayRestriction
      (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
        ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm⟩)
      (reesClosedLocalizedThickeningFrobenius I p hp hR hA
        (projectiveLaurentDenominator R T) n e z.val)
  exact projectiveLocalizedPowerMap_restriction
    (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
    (reesClosedRingThickeningFrobenius I p hp hA n e) (p ^ e)
    (reesClosedRingThickeningFrobenius_algebraMap I p hp hA n e)
    (reesClosedRingThickeningFrobenius_scalar I p hp hR hA n e)
    (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm z.val

/-- 実際の標準開の厚化 Frobenius を、係数作用を制限した図式の射にする。 -/
def reesClosedChartThickeningFrobeniusNatTrans (n e : ℕ) (d : ℤ) :
    projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d ⟶
    projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)
      (((p ^ e : ℕ) : ℤ) * d) ⋙
        ModuleCat.restrictScalars (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e)) where
  app T := reesClosedChartThickeningFrobeniusApp I G p hp hR hA n e d T
  naturality {T U} h := reesClosedChartThickeningFrobeniusApp_naturality I G p hp hR hA n e d h

/-- 実際の閉厚化の Čech H の、厚化を経由する反復 Frobenius。
BST13 Lemma 3.9(1) と BS17 Lemma 4.6(i) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedCechThickeningFrobenius (n e : ℕ) (d : ℤ) (q : ℕ) :
    (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d)).homology q
      →ₛₗ[frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e)]
    (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)
      (((p ^ e : ℕ) : ℤ) * d))).homology q :=
  projectiveCechSemilinearHomologyMap
    (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e)) _ _
    (reesClosedChartThickeningFrobeniusNatTrans I G p hp hR hA n e d) q

end SerrePositivity.AlgebraicGeometry
