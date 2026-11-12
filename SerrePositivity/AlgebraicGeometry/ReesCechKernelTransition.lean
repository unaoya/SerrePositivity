module

public import SerrePositivity.AlgebraicGeometry.ReesCechKernel
public import SerrePositivity.AlgebraicGeometry.LinearMapZeroOnSpan

/-!
概要：Čech 核の遷移と、十分 I 進的な単項式による零化を扱う。
方針：遷移と包含の可換式、次数移動の因子分解を核の元に評価する。
規約：有限な生成元を選ぶ段階だけ Noether 性を使う。
使われ方：斉次生成元の次数の上界から、核の遷移の一様零化へ進む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesKernelTransitionModule (d : ℤ) (q : ℕ) :
    Module (reesAlgebra I) (ReesIntegerCechDirectSum (ι := ι) I G d q) :=
  reesAdicCechIntegerDirectSumTransportedModule (ι := ι) I G d q

/-- 各段の Čech 包含の核は、I 進遷移で保たれる。 -/
theorem reesAdicProjectiveCechTransition_mem_kernel
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveCechStage (ι := ι) I G i d q)
    (hx : (reesAdicProjectiveCechToModule (ι := ι) I G i d q).hom x = 0) :
    (reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom
      ((reesAdicProjectiveCechTransition (ι := ι) I G i j h d q).hom x) = 0 := by
  have hcat := reesAdicProjectiveCechToModule_transition (ι := ι) I G i j h d q
  exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcat) x).trans hx

/-- 十分 I 進的な係数による次数移動は、Čech 核の元の遷移を零にする。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechTransition_degreeShift_zero
    (i j n : ℕ) (hn : n ≤ i) (a : R) (ha : a ∈ I ^ i) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveCechStage (ι := ι) I G j d q)
    (hx : (reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom x = 0) :
    (reesAdicProjectiveCechTransition (ι := ι) I G (i + j) n
      (hn.trans (Nat.le_add_right i j)) d q).hom
        ((reesAdicProjectiveDegreeShiftCechHomologyMap (ι := ι) I G i j a ha d q).hom x) =
      0 := by
  have hcat := reesAdicProjectiveCechTransition_degreeShift_factor
    (ι := ι) I G i j n hn a ha d q
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcat) x
  change (reesAdicProjectiveCechTransition (ι := ι) I G (i + j) n
      (hn.trans (Nat.le_add_right i j)) d q).hom
        ((reesAdicProjectiveDegreeShiftCechHomologyMap (ι := ι) I G i j a ha d q).hom x) =
    (reesAdicProjectiveCechCoefficientLift (ι := ι) I G n a
      ((Ideal.pow_le_pow_right hn) ha) d q).hom
        ((reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom x) at h
  rw [hx, map_zero] at h
  exact h

/-- 実際の Čech 核は、次数に一様な上界のある有限個の斉次元で生成される。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechKernel_bounded_homogeneous_generators [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    ∃ c : ℕ, ∃ s : Finset (ReesIntegerCechDirectSum (ι := ι) I G d q),
      Submodule.span (reesAlgebra I) (↑s : Set _) =
        reesAdicProjectiveCechKernel (ι := ι) I G d q ∧
      ∀ z ∈ s, ∃ j, j ≤ c ∧
        ∃ x : reesAdicProjectiveCechStage (ι := ι) I G j d q,
          (reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom x = 0 ∧
          z = DirectSum.lof R ℕ
            (fun n ↦ reesAdicProjectiveCechStage (ι := ι) I G n d q) j x := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    reesAdicProjectiveCechKernel_finite_homogeneous_generators (ι := ι) I G d q
  have hdeg : ∀ z : s, ∃ j,
      ∃ x : reesAdicProjectiveCechStage (ι := ι) I G j d q,
        (reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom x = 0 ∧
        (z : ReesIntegerCechDirectSum (ι := ι) I G d q) = DirectSum.lof R ℕ
          (fun n ↦ reesAdicProjectiveCechStage (ι := ι) I G n d q) j x :=
    fun z ↦ hs z.property
  choose deg x hx heq using hdeg
  refine ⟨s.attach.sup deg, s, hspan, ?_⟩
  intro z hz
  exact ⟨deg ⟨z, hz⟩, Finset.le_sup (s.mem_attach ⟨z, hz⟩),
    x ⟨z, hz⟩, hx ⟨z, hz⟩, heq ⟨z, hz⟩⟩

end SerrePositivity.AlgebraicGeometry
