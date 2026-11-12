module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationCongr

/-!
概要：斉次局所化の直和への移送を、周囲の局所化と各成分の分数で記述する。
方針：直和比較の値の公式と、線形同値の逆による局所化の写像を合成する。
規約：分子の指定部分を対応させる加群の同値を入力する。
使われ方：Rees 加群の標準開比較の自然性と、Rees 単項式の作用の追跡。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum

variable {R S κ : Type*} [CommRing R] [CommRing S] [Algebra R S] [DecidableEq κ]
variable {F : κ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
variable [∀ i, Module S (F i)] [∀ i, IsScalarTower R S (F i)]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (f : S) (V : ∀ i, ℕ → Submodule R (F i)) (W : ℕ → Submodule R N)
variable (e : (⨁ i, F i) ≃ₗ[S] N)
variable (he : ∀ k x, e x ∈ W k ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ V i k))
variable (hstep : ∀ (i : κ) (k : ℕ) (m : V i k), f • m.val ∈ V i (k + 1))

/-- 斉次成分の直和への移送は、周囲の局所化の二つの同値の合成に一致する。 -/
theorem projectiveGradedLocalizedDirectSumTransport_val (z : projectiveGradedAway f W) :
    DirectSum.lmap (fun i ↦ (projectiveGradedAway f (V i)).subtype)
        (projectiveGradedLocalizedDirectSumTransport f V W e he hstep z) =
      projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) F
        (projectiveLocalizedModuleCongr (Submonoid.powers f) e.symm z.val) := by
  simp only [projectiveGradedLocalizedDirectSumTransport, LinearEquiv.trans_apply]
  rw [projectiveGradedLocalizedDirectSumLinearEquiv_val]
  rfl

/-- 斉次成分の移送の各成分を、周囲の局所化で計算する。 -/
theorem projectiveGradedLocalizedDirectSumTransport_component_val
    (z : projectiveGradedAway f W) (i : κ) :
    ((projectiveGradedLocalizedDirectSumTransport f V W e he hstep z) i).val =
      (projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) F
        (projectiveLocalizedModuleCongr (Submonoid.powers f) e.symm z.val)) i :=
  congrArg (fun x ↦ x i) (projectiveGradedLocalizedDirectSumTransport_val f V W e he hstep z)

/-- 斉次分数の移送は、分子に逆の加群同値を適用し、同じ分母で各成分を割る。 -/
theorem projectiveGradedLocalizedDirectSumTransport_fraction
    (k : ℕ) (m : W k) (z : projectiveGradedAway f W)
    (hz : projectiveGradedFraction f W k m = z.val) (i : κ) :
    ((projectiveGradedLocalizedDirectSumTransport f V W e he hstep z) i).val =
      LocalizedModule.mk (e.symm m.val i) (projDenominator f k) := by
  rw [projectiveGradedLocalizedDirectSumTransport_component_val, ← hz,
    projectiveGradedFraction_apply, projectiveLocalizedModuleCongr_mk,
    projectiveLocalizedDirectSumLinearEquiv_mk_component]

end SerrePositivity.AlgebraicGeometry
