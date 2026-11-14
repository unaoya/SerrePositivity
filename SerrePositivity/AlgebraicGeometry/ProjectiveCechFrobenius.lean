module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedFrobenius
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSemilinearMap

/-!
概要：次数付き環の実際の標準開の Frobenius を、Čech コホモロジーへ送る。
方針：指定次数部分への制限を各標準開で作り、制限射との可換性から図式を構成する。
規約：捻り d は p*d へ移す。空の標準開も含み、局所化の非自明性を仮定しない。
使われ方：射影版の形式関数と BST13 の正次数の Frobenius の議論を接続する。
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
variable (p : ℕ) (hp : p.Prime) [ExpChar R p] (hz : (p : A) = 0)
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance projectiveCechFrobeniusIntGradedAction :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt G) := projectiveNatGradingIntSMul (ι := ι) G

/-- 各標準開の実際の Frobenius は、捻り d の部分を捻り p*d の部分へ送る。 -/
def projectiveNatGradedChartFrobenius (T : Finset ι) (d : ℤ) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T →ₛₗ[frobenius R p]
      (projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d)).obj T :=
  projectiveGradedAwayFrobenius p hp (projectiveLaurentDenominator R T)
    (fun n ↦ projectiveNatGradingInt G (d + n • (T.card : ℤ)))
    (fun n ↦ projectiveNatGradingInt G ((p : ℤ) * d + n • (T.card : ℤ))) hz
    (projectiveGradedChart_mul_denominator (projectiveNatGradingInt G) T d)
    (fun n m ↦ projectiveNatGradingInt_chart_pow_mem p G d (T.card : ℤ) n m)

/-- 各標準開の指定次数の Frobenius は、周囲の局所化環の p 乗の制限である。 -/
theorem projectiveNatGradedChartFrobenius_val (T : Finset ι) (d : ℤ)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) :
    (projectiveNatGradedChartFrobenius p hp hz G T d z).val =
      projectiveLocalizedFrobenius p hp
        (Submonoid.powers (projectiveLaurentDenominator R T)) hz z.val := rfl

/-- 実際の標準開の Frobenius を、係数作用を制限した図式の射にする。 -/
def projectiveNatGradedChartFrobeniusNatTrans (d : ℤ) :
    projectiveNatGradedModuleChartDiagram (ι := ι) G d ⟶
      projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d) ⋙
        ModuleCat.restrictScalars (frobenius R p) where
  app T := by
    let Y := (projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d)).obj T
    let F := projectiveNatGradedChartFrobenius p hp hz G T d
    exact ModuleCat.ofHom
      (X := (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T)
      (Y := (ModuleCat.restrictScalars (frobenius R p)).obj Y)
      { toFun := fun z ↦ F z
        map_add' := F.map_add
        map_smul' r z := map_smulₛₗ F r z }
  naturality {T U} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change projectiveLocalizedFrobenius p hp
        (Submonoid.powers (projectiveLaurentDenominator R U)) hz
          (projectiveModuleAwayRestriction
            (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
              ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm⟩) z.val) =
      projectiveModuleAwayRestriction
        (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
          ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm⟩)
        (projectiveLocalizedFrobenius p hp
          (Submonoid.powers (projectiveLaurentDenominator R T)) hz z.val)
    exact (projectiveLocalizedFrobenius_restriction p hp
      (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm hz z.val).symm

/-- 実際の構造層の標準開から得た、Čech コホモロジーの Frobenius 半線形写像。
原典 BST13 Lemma 3.9(1) と BS17 Lemma 4.6(i) の Hⁱ の Frobenius に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatGradedCechFrobenius (d : ℤ) (q : ℕ) :
    (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q
      →ₛₗ[frobenius R p]
    (fullCechComplex
      (projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d))).homology q :=
  projectiveCechSemilinearHomologyMap (frobenius R p)
    (projectiveNatGradedModuleChartDiagram (ι := ι) G d)
    (projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d))
    (projectiveNatGradedChartFrobeniusNatTrans p hp hz G d) q

end SerrePositivity.AlgebraicGeometry
