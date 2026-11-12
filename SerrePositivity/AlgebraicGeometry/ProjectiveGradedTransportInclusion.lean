module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedTransportValues

/-!
概要：斉次局所化の直和比較と、各成分の包含との両立性。
方針：斉次分数の各成分を計算し、包含の添字以外で零であることを示す。
規約：分子の次数を対応させる加群同値を入力する。
使われ方：Rees の Čech 直和比較で、各 Rees 次数からの包含を追う。
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

include he

/-- 各成分の包含と同値の合成は、分子の指定部分を保つ。 -/
theorem projectiveGradedTransportInclusion_mem (i : κ) (k : ℕ)
    (m : F i) (hm : m ∈ V i k) :
    e (DirectSum.lof S κ F i m) ∈ W k := by
  apply (he k _).mpr
  rw [mem_projectiveDirectSumSubmodule]
  intro j
  by_cases h : j = i
  · subst j
    simpa only [DirectSum.lof_apply] using hm
  · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne i j m h]
    exact (V j k).zero_mem

/-- 直和の斉次局所化比較は、各成分からの局所化した包含を直和の包含へ写す。 -/
theorem projectiveGradedLocalizedDirectSumTransport_inclusion (i : κ)
    (z : projectiveGradedAway f (V i)) :
    projectiveGradedLocalizedDirectSumTransport f V W e he hstep
        (projectiveGradedAwayMap f (V i) W
          (e.toLinearMap.comp (DirectSum.lof S κ F i))
          (projectiveGradedTransportInclusion_mem V W e he i) z) =
      DirectSum.lof R κ (fun j ↦ projectiveGradedAway f (V j)) i z := by
  obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f (V i) (hstep i) z.val).mp z.property
  let u := e.toLinearMap.comp (DirectSum.lof S κ F i)
  let hu := projectiveGradedTransportInclusion_mem V W e he i
  have hmW := projectiveGradedAwayMap_fraction f (V i) W u hu n m z hm
  apply DFinsupp.ext
  intro j
  apply Subtype.ext
  rw [projectiveGradedLocalizedDirectSumTransport_fraction f V W e he hstep n
    ⟨u m.val, hu n m.val m.property⟩ _ hmW.symm j]
  change LocalizedModule.mk (e.symm (e (DirectSum.lof S κ F i m.val)) j)
    (projDenominator f n) = _
  rw [e.symm_apply_apply]
  by_cases h : j = i
  · subst j
    simpa only [DirectSum.lof_apply, projectiveGradedFraction_apply] using hm
  · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne i j m.val h,
      DirectSum.of_eq_of_ne (β := fun j ↦ projectiveGradedAway f (V j)) i j z h, ZeroMemClass.coe_zero, LocalizedModule.zero_mk]

end SerrePositivity.AlgebraicGeometry
