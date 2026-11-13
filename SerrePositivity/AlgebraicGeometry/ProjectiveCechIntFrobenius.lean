module

public import SerrePositivity.AlgebraicGeometry.ProjectiveChartIteratedFrobenius
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntRestriction

/-!
概要：捻り零の Čech 図式に、反復 Frobenius の整数線形自己射を与える。
方針：各標準開の実際の冪写像を使い、反復則を分数の値で照合する。
規約：係数環の作用を整数へ制限するだけで、標準開の図式は変えない。
使われ方：F6 の Frobenius 順極限と、厚化による因子分解。
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
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 捻り零の標準開図式の整数線形な反復 Frobenius。 -/
def projectiveCechIntFrobeniusDiagram (e : ℕ) :
    projectiveNatGradedModuleChartDiagram (ι := ι) G 0 ⋙
        ModuleCat.restrictScalars (Int.castRingHom R) ⟶
    projectiveNatGradedModuleChartDiagram (ι := ι) G 0 ⋙
        ModuleCat.restrictScalars (Int.castRingHom R) where
  app T := by
    let X := (ModuleCat.restrictScalars (Int.castRingHom R)).obj
      ((projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T)
    let F := projectiveChartIteratedFrobenius G p hp hR hA T e
    exact ModuleCat.ofHom (X := X) (Y := X)
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
    apply Subtype.ext
    change (projectiveChartIteratedFrobenius G p hp hR hA U e
      (((projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map h).hom z)).val = _
    rw [projectiveChartIteratedFrobenius_val]
    change (projectiveModuleAwayRestriction
      (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
        ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm⟩) z.val) ^ (p ^ e) =
      projectiveModuleAwayRestriction
        (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
          ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm⟩)
        (projectiveChartIteratedFrobenius G p hp hR hA T e z).val
    rw [projectiveChartIteratedFrobenius_val]
    exact (projectiveModuleAwayRestriction_pow (p ^ e)
      (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm z.val).symm

/-- 零回の反復は標準開図式の恒等射。 -/
theorem projectiveCechIntFrobeniusDiagram_zero :
    projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA 0 = 𝟙 _ := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change (projectiveChartIteratedFrobenius G p hp hR hA T 0 z).val = z.val
  rw [projectiveChartIteratedFrobenius_val, pow_zero, pow_one]

/-- 反復回数の加法は標準開図式の射の合成に対応する。 -/
theorem projectiveCechIntFrobeniusDiagram_add (e f : ℕ) :
    projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA (e + f) =
      projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA e ≫
        projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA f := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change (projectiveChartIteratedFrobenius G p hp hR hA T (e + f) z).val =
    (projectiveChartIteratedFrobenius G p hp hR hA T f
      (projectiveChartIteratedFrobenius G p hp hR hA T e z)).val
  rw [projectiveChartIteratedFrobenius_val, projectiveChartIteratedFrobenius_val,
    projectiveChartIteratedFrobenius_val, ← pow_mul, ← pow_add]

end SerrePositivity.AlgebraicGeometry
