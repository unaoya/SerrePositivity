module

public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionH0Comparison
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechHomology

/-!
概要：閉厚化への実際の切断代数の制限の核に、Rees の一様な I 進評価を移す。
方針：射影に自然な H⁰ の同型で核を移し、逆の線形同型でイデアルの作用を戻す。
規約：切断代数自身の I 冪による消滅を仮定しない。
使われ方：F7 の B/IB と閉厚化の切断環の比較の核が冪零であることの入力。
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
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R)
local instance reesSectionKernelGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 切断環の実際の制限の核は、Rees 側の Čech H⁰ の射の核に対応する。 -/
theorem reesClosedHomogeneousSectionProjection_eq_zero_iff (n : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) G) :
    reesClosedHomogeneousSectionProjection G I n a = 0 ↔
      (reesAdicProjectiveClosedCechProjection (ι := ι) I G n 0 0).hom
        (projectiveHomogeneousSectionNatH0Equiv G a) = 0 := by
  rw [← reesClosedHomogeneousSectionH0Equiv_reesProjection]
  exact (reesClosedHomogeneousSectionH0Equiv G I n).map_eq_zero_iff.symm

/-- 閉厚化への切断代数の制限の核の一様な I 進評価。
原典 Stacks 30.20.4(1) の H⁰ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedHomogeneousSectionProjection_kernel_bound
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A] :
    ∃ c : ℕ, ∀ n, c ≤ n →
      LinearMap.ker (reesClosedHomogeneousSectionProjection (ι := ι) G I n).toLinearMap ≤
        I ^ (n - c) • (⊤ : Submodule R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) := by
  obtain ⟨c, hc⟩ := reesAdicProjectiveClosedCechProjection_kernel_bound (ι := ι) I G 0 0
  refine ⟨c, ?_⟩
  intro n hn a ha
  have hz := (reesClosedHomogeneousSectionProjection_eq_zero_iff G I n a).mp ha
  have hm := hc n hn hz
  have hback := Submodule.smul_top_le_comap_smul_top (I ^ (n - c))
    (projectiveHomogeneousSectionNatH0Equiv (ι := ι) G).symm.toLinearMap hm
  simpa only [Submodule.mem_comap, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using hback

/-- 十分厚い閉厚化への制限で消える切断は、基底の指定冪の拡大イデアルに入る。 -/
theorem reesClosedHomogeneousSectionProjection_kernel_ideal_bound
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A] :
    ∃ c : ℕ, ∀ n, c ≤ n → ∀ a : projectiveHomogeneousSectionAlgebra (ι := ι) G,
      reesClosedHomogeneousSectionProjection G I n a = 0 →
        a ∈ (I ^ (n - c)).map
          (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) := by
  obtain ⟨c, hc⟩ := reesClosedHomogeneousSectionProjection_kernel_bound (ι := ι) G I
  refine ⟨c, ?_⟩
  intro n hn a ha
  have hm := hc n hn ha
  rw [Ideal.smul_top_eq_map] at hm
  exact hm

end SerrePositivity.AlgebraicGeometry
