module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationMaps
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
概要：標準開の斉次局所化と Čech 複体への写像は、加法と合成を保つ。
方針：局所化の指定次数成分の写像の公式を、自然変換の各成分で使う。
規約：写像は次数を保つ。加群は同じ宇宙に置く。
使われ方：有限自由加群の座標ごとの分裂を Čech 複体へ送る。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped BigOperators

universe u

variable {ι R : Type*} [DecidableEq ι] [Fintype ι] [CommRing R]
variable {M N P : Type u}
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable [IsScalarTower R (MvPolynomial ι R) P]
variable (G : ℤ → Submodule R M) (H : ℤ → Submodule R N) (J : ℤ → Submodule R P)
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) G]
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) H]
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) J]

/-- 標準開の係数図式への写像は恒等写像を保つ。 -/
theorem projectiveGradedModuleChartMap_id (d : ℤ) :
    projectiveGradedModuleChartMap (ι := ι) G G d LinearMap.id (fun _ _ h ↦ h) =
      𝟙 (projectiveGradedModuleChartDiagram (ι := ι) G d) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  exact projectiveGradedAwayMap_id _ _

/-- 標準開の係数図式への写像は合成を保つ。 -/
theorem projectiveGradedModuleChartMap_comp (d : ℤ)
    (f : M →ₗ[MvPolynomial ι R] N) (g : N →ₗ[MvPolynomial ι R] P)
    (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n) (hg : ∀ n, ∀ m ∈ H n, g m ∈ J n) :
    projectiveGradedModuleChartMap (ι := ι) G H d f hf ≫
        projectiveGradedModuleChartMap (ι := ι) H J d g hg =
      projectiveGradedModuleChartMap (ι := ι) G J d (g.comp f)
        (fun n m hm ↦ hg n _ (hf n m hm)) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  exact (projectiveGradedAwayMap_comp _ _ _ _ f g
    (fun n ↦ hf (d + n • (T.card : ℤ)))
    (fun n ↦ hg (d + n • (T.card : ℤ)))).symm

/-- 標準開の係数図式への写像は有限和を保つ。 -/
theorem projectiveGradedModuleChartMap_sum {κ : Type*} (d : ℤ) (t : Finset κ)
    (f : κ → M →ₗ[MvPolynomial ι R] N)
    (hf : ∀ j, ∀ n, ∀ m ∈ G n, f j m ∈ H n)
    (hsum : ∀ n, ∀ m ∈ G n, (∑ j ∈ t, f j) m ∈ H n) :
    projectiveGradedModuleChartMap (ι := ι) G H d (∑ j ∈ t, f j) hsum =
      ∑ j ∈ t, projectiveGradedModuleChartMap (ι := ι) G H d (f j) (hf j) := by
  apply NatTrans.ext
  funext T
  rw [NatTrans.app_sum]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  apply LinearMap.ext
  intro z
  rw [LinearMap.sum_apply]
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change IsLocalizedModule.map (Submonoid.powers (projectiveLaurentDenominator R T))
      (LocalizedModule.mkLinearMap (Submonoid.powers (projectiveLaurentDenominator R T)) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (projectiveLaurentDenominator R T)) N)
      (∑ j ∈ t, f j) z.val =
    ∑ j ∈ t, IsLocalizedModule.map (Submonoid.powers (projectiveLaurentDenominator R T))
      (LocalizedModule.mkLinearMap (Submonoid.powers (projectiveLaurentDenominator R T)) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (projectiveLaurentDenominator R T)) N)
      (f j) z.val
  rw [map_sum, LinearMap.sum_apply]

/-- 係数の加法を、全タプル Čech 複体の加法へ送る。 -/
instance : (fullCechComplexFunctor (R := R) (ι := ι)).Additive where
  map_add := by
    intro D E f g
    ext q a
    rfl

section Ordered

variable [LinearOrder ι]

/-- 係数の加法を、狭義増加 Čech 複体の加法へ送る。 -/
instance : (orderedCechComplexFunctor (R := R) (ι := ι)).Additive where
  map_add := by
    intro D E f g
    ext q a
    rfl

end Ordered

end SerrePositivity.AlgebraicGeometry
