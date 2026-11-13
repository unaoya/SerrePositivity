module

public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousSectionTransition
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechStabilization

/-!
概要：実際の閉厚化の切断代数の像の安定化。
方針：制限と遷移に自然な比較で、Rees の Čech H⁰ の像の等式を移す。
規約：安定した像は元の切断代数からの実際の制限の像。
使われ方：F7 の Frobenius の十分高い冪を元の切断の像へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance reesSectionImageGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 閉厚化の切断代数の遷移の像は、一様に遅らせれば元の切断代数の制限の像に等しい。
原典 Stacks 30.20.4(3) の H⁰ の像の安定化に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedHomogeneousSectionTransition_range_stabilizes
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A] :
    ∃ c : ℕ, ∀ n l (hl : n + c ≤ l),
      LinearMap.range (reesClosedHomogeneousSectionTransition (ι := ι) I G l n
        ((Nat.le_add_right n c).trans hl)).toLinearMap =
      LinearMap.range (reesClosedHomogeneousSectionProjection (ι := ι) G I n).toLinearMap := by
  obtain ⟨c, hc⟩ := reesAdicProjectiveClosedCechTransition_range_stabilizes (ι := ι) I G 0 0
  refine ⟨c, ?_⟩
  intro n l hl
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    have hx : reesClosedHomogeneousSectionH0Equiv G I n
        (reesClosedHomogeneousSectionTransition I G l n ((Nat.le_add_right n c).trans hl) a) ∈
        LinearMap.range (reesAdicProjectiveClosedCechTransition (ι := ι) I G l n
          ((Nat.le_add_right n c).trans hl) 0 0).hom :=
      ⟨reesClosedHomogeneousSectionH0Equiv G I l a,
        (reesClosedHomogeneousSectionH0Equiv_transition I G l n _ a).symm⟩
    rw [hc n l hl] at hx
    obtain ⟨b, hb⟩ := hx
    refine ⟨(projectiveHomogeneousSectionNatH0Equiv G).symm b, ?_⟩
    apply (reesClosedHomogeneousSectionH0Equiv G I n).injective
    change reesClosedHomogeneousSectionH0Equiv G I n
      (reesClosedHomogeneousSectionProjection G I n _) = _
    rw [reesClosedHomogeneousSectionH0Equiv_reesProjection, LinearEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨a, rfl⟩
    have hx : reesClosedHomogeneousSectionH0Equiv G I n
        (reesClosedHomogeneousSectionProjection G I n a) ∈
        LinearMap.range (reesAdicProjectiveClosedCechProjection (ι := ι) I G n 0 0).hom :=
      ⟨projectiveHomogeneousSectionNatH0Equiv G a,
        (reesClosedHomogeneousSectionH0Equiv_reesProjection G I n a).symm⟩
    rw [← hc n l hl] at hx
    obtain ⟨b, hb⟩ := hx
    refine ⟨(reesClosedHomogeneousSectionH0Equiv G I l).symm b, ?_⟩
    apply (reesClosedHomogeneousSectionH0Equiv G I n).injective
    change reesClosedHomogeneousSectionH0Equiv G I n
      (reesClosedHomogeneousSectionTransition I G l n _ _) = _
    rw [reesClosedHomogeneousSectionH0Equiv_transition, LinearEquiv.apply_symm_apply]
    exact hb

end SerrePositivity.AlgebraicGeometry
