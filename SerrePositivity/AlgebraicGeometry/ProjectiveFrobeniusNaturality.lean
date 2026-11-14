module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobenius
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSemilinearNaturality

/-!
概要：実際の局所化と標準開の Frobenius を、次数を保つ代数の射に自然にする。
方針：局所化の分数表示で環の冪の保存を使い、係数図式の四角形へ送る。
規約：局所化が零環の場合も含める。
使われ方：実際の閉厚化の商写像と Frobenius の Čech 写像の整合性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
section Localization
variable {P A B : Type*} [CommRing P] [CommRing A] [CommRing B]
variable [Algebra P A] [Algebra P B]
variable (p : ℕ) (hp : p.Prime) (S : Submonoid P) (f : A →ₐ[P] B)

/-- 実際の局所化の Frobenius は、代数の環準同型が誘導する局所化の射に自然。 -/
theorem projectiveLocalizedFrobenius_map (hzA : (p : A) = 0) (hzB : (p : B) = 0)
    (z : LocalizedModule S A) :
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S A)
        (LocalizedModule.mkLinearMap S B) f.toLinearMap
        (projectiveLocalizedFrobenius p hp S hzA z) =
      projectiveLocalizedFrobenius p hp S hzB
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S A)
          (LocalizedModule.mkLinearMap S B) f.toLinearMap z) := by
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    rw [projectiveLocalizedFrobenius_mk, IsLocalizedModule.map_LocalizedModules,
      IsLocalizedModule.map_LocalizedModules, projectiveLocalizedFrobenius_mk]
    congr 1
    exact f.map_pow m p

end Localization
end SerrePositivity.AlgebraicGeometry

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
local instance projectiveFrobeniusNaturalIntGradedAction :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt G) := projectiveNatGradingIntSMul (ι := ι) G


variable {B : Type u} [CommRing B] [Algebra R B] [Algebra (MvPolynomial ι R) B]
variable [IsScalarTower R (MvPolynomial ι R) B]
variable (hzB : (p : B) = 0)
variable (H : ℕ → Submodule R B) [SetLike.GradedMonoid H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : A →ₐ[MvPolynomial ι R] B) (hf : ∀ j, ∀ a ∈ G j, f a ∈ H j)

/-- 標準開の実際の Frobenius の自然変換は、次数を保つ代数の射と可換。 -/
theorem projectiveNatGradedChartFrobeniusNatTrans_naturality (d : ℤ) :
    projectiveNatGradedModuleChartMap G H f.toLinearMap hf d ≫
        projectiveNatGradedChartFrobeniusNatTrans p hp hzB H d =
      projectiveNatGradedChartFrobeniusNatTrans p hp hz G d ≫
        Functor.whiskerRight
          (projectiveNatGradedModuleChartMap G H f.toLinearMap hf ((p : ℤ) * d))
          (ModuleCat.restrictScalars (frobenius R p)) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change projectiveLocalizedFrobenius p hp
      (Submonoid.powers (projectiveLaurentDenominator R T)) hzB
        (IsLocalizedModule.map (Submonoid.powers (projectiveLaurentDenominator R T))
          (LocalizedModule.mkLinearMap _ A) (LocalizedModule.mkLinearMap _ B)
          f.toLinearMap z.val) =
    IsLocalizedModule.map (Submonoid.powers (projectiveLaurentDenominator R T))
      (LocalizedModule.mkLinearMap _ A) (LocalizedModule.mkLinearMap _ B) f.toLinearMap
      (projectiveLocalizedFrobenius p hp
        (Submonoid.powers (projectiveLaurentDenominator R T)) hz z.val)
  exact (projectiveLocalizedFrobenius_map p hp _ f hz hzB z.val).symm

/-- 実際の標準開の Čech Frobenius は、次数を保つ代数の射に自然。
原典 BS17 Lemma 4.6(i) と BST13 Lemma 3.9(1) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedCechFrobenius_naturality (d : ℤ) (q : ℕ)
    (x : (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q) :
    projectiveNatGradedCechFrobenius p hp hzB H d q
        ((projectiveNatGradedModuleCechHomologyMap G H f.toLinearMap hf d q).hom x) =
      (projectiveNatGradedModuleCechHomologyMap G H f.toLinearMap hf ((p : ℤ) * d) q).hom
        (projectiveNatGradedCechFrobenius p hp hz G d q x) :=
  projectiveCechSemilinearHomologyMap_naturality (frobenius R p)
    (projectiveNatGradedChartFrobeniusNatTrans p hp hz G d)
    (projectiveNatGradedChartFrobeniusNatTrans p hp hzB H d)
    (projectiveNatGradedModuleChartMap G H f.toLinearMap hf d)
    (projectiveNatGradedModuleChartMap G H f.toLinearMap hf ((p : ℤ) * d))
    (projectiveNatGradedChartFrobeniusNatTrans_naturality p hp hz G hzB H f hf d) q x

end SerrePositivity.AlgebraicGeometry
