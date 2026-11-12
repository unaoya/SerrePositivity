module

public import SerrePositivity.AlgebraicGeometry.ReesCechKernelTransition

/-!
概要：実際の Čech 包含の核は、I 進遷移に関して一様に零になる。
方針：有限な斉次生成元の次数を抑え、単項式による移動と遷移の因子分解を使う。
規約：零化の遅れは Proj 次数・Čech 次数に依存してよい。
使われ方：閉厚化への Čech 写像の像の安定化と、形式関数の完備化比較への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum BigOperators

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesKernelVanishingModule (d : ℤ) (q : ℕ) :
    Module (reesAlgebra I) (ReesIntegerCechDirectSum (ι := ι) I G d q) :=
  reesAdicCechIntegerDirectSumTransportedModule (ι := ι) I G d q

/-- 直和の第 l 成分を取り、そこから第 n 段へ遷移する R 線形写像。 -/
def reesAdicProjectiveCechTransitionComponent
    (l n : ℕ) (h : n ≤ l) (d : ℤ) (q : ℕ) :
    ReesIntegerCechDirectSum (ι := ι) I G d q →ₗ[R]
      reesAdicProjectiveCechStage (ι := ι) I G n d q :=
  (reesAdicProjectiveCechTransition (ι := ι) I G l n h d q).hom.comp
    (DirectSum.component R ℕ
      (fun j ↦ reesAdicProjectiveCechStage (ι := ι) I G j d q) l)

/-- 十分高い次数の成分の遷移は、低次数の斉次核の元の単項式倍で零。 -/
theorem reesAdicProjectiveCechTransitionComponent_monomial_kernel_zero
    (l n c : ℕ) (h : n ≤ l) (hl : n + c ≤ l)
    (i j : ℕ) (hj : j ≤ c) (a : R) (ha : a ∈ I ^ i) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveCechStage (ι := ι) I G j d q)
    (hx : (reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom x = 0) :
    reesAdicProjectiveCechTransitionComponent (ι := ι) I G l n h d q
      ((⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
        DirectSum.lof R ℕ
          (fun k ↦ reesAdicProjectiveCechStage (ι := ι) I G k d q) j x) = 0 := by
  rw [reesAdicCechIntegerDirectSum_monomial_smul_lof (ι := ι) I G i j a ha d q x]
  by_cases hij : i + j = l
  · subst l
    have hn : n ≤ i := by omega
    change (reesAdicProjectiveCechTransition (ι := ι) I G (i + j) n h d q).hom
      ((DirectSum.lof R ℕ
        (fun k ↦ reesAdicProjectiveCechStage (ι := ι) I G k d q) (i + j)
        ((reesAdicProjectiveDegreeShiftCechHomologyMap
          (ι := ι) I G i j a ha d q).hom x)) (i + j)) = 0
    rw [DirectSum.lof_apply]
    exact reesAdicProjectiveCechTransition_degreeShift_zero
      (ι := ι) I G i j n hn a ha d q x hx
  · change (reesAdicProjectiveCechTransition (ι := ι) I G l n h d q).hom
      ((DirectSum.lof R ℕ
        (fun k ↦ reesAdicProjectiveCechStage (ι := ι) I G k d q) (i + j)
        ((reesAdicProjectiveDegreeShiftCechHomologyMap
          (ι := ι) I G i j a ha d q).hom x)) l) = 0
    simp [DirectSum.lof_eq_of, DirectSum.of_apply, hij]

/-- 同じ成分の遷移は、低次数の斉次核の元の任意の Rees 倍で零。 -/
theorem reesAdicProjectiveCechTransitionComponent_smul_kernel_zero
    (l n c : ℕ) (h : n ≤ l) (hl : n + c ≤ l)
    (j : ℕ) (hj : j ≤ c) (b : reesAlgebra I) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveCechStage (ι := ι) I G j d q)
    (hx : (reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom x = 0) :
    reesAdicProjectiveCechTransitionComponent (ι := ι) I G l n h d q
      (b • DirectSum.lof R ℕ
        (fun k ↦ reesAdicProjectiveCechStage (ι := ι) I G k d q) j x) = 0 := by
  rw [reesAlgebra.as_sum_support b]
  simp only [Finset.sum_smul, map_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  exact reesAdicProjectiveCechTransitionComponent_monomial_kernel_zero
    (ι := ι) I G l n c h hl i j hj (b.val.coeff i) (b.property i) d q x hx

/-- 低次数の斉次核で生成した Rees 部分加群では、十分先の成分の遷移は零。 -/
theorem reesAdicProjectiveCechTransitionComponent_zero_of_span
    (d : ℤ) (q c : ℕ) (s : Set (ReesIntegerCechDirectSum (ι := ι) I G d q))
    (hs : ∀ y ∈ s, ∃ j, j ≤ c ∧
      ∃ v : reesAdicProjectiveCechStage (ι := ι) I G j d q,
        (reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom v = 0 ∧
        y = DirectSum.lof R ℕ
          (fun k ↦ reesAdicProjectiveCechStage (ι := ι) I G k d q) j v)
    (n l : ℕ) (h : n ≤ l) (hl : n + c ≤ l)
    (z : ReesIntegerCechDirectSum (ι := ι) I G d q)
    (hz : z ∈ Submodule.span (reesAlgebra I) s) :
    reesAdicProjectiveCechTransitionComponent (ι := ι) I G l n h d q z = 0 := by
  let f := reesAdicProjectiveCechTransitionComponent (ι := ι) I G l n h d q
  have hgen : ∀ y ∈ s, ∀ b : reesAlgebra I, f (b • y) = 0 := by
    intro y hy b
    obtain ⟨j, hj, v, hv, rfl⟩ := hs y hy
    exact reesAdicProjectiveCechTransitionComponent_smul_kernel_zero
      (ι := ι) I G l n c h hl j hj b d q v hv
  exact linearMap_zero_on_span_of_smul_generators
    (R := R) (B := reesAlgebra I)
    (E := ReesIntegerCechDirectSum (ι := ι) I G d q)
    (N := reesAdicProjectiveCechStage (ι := ι) I G n d q) f s hgen z hz

/-- 次数が c 以下の斉次核で生成されれば、c だけ遅らせた核の遷移は零。 -/
theorem reesAdicProjectiveCechKernel_transition_zero_of_bounded_generators
    (d : ℤ) (q c : ℕ) (s : Set (ReesIntegerCechDirectSum (ι := ι) I G d q))
    (hspan : Submodule.span (reesAlgebra I) s =
      reesAdicProjectiveCechKernel (ι := ι) I G d q)
    (hs : ∀ y ∈ s, ∃ j, j ≤ c ∧
      ∃ v : reesAdicProjectiveCechStage (ι := ι) I G j d q,
        (reesAdicProjectiveCechToModule (ι := ι) I G j d q).hom v = 0 ∧
        y = DirectSum.lof R ℕ
          (fun k ↦ reesAdicProjectiveCechStage (ι := ι) I G k d q) j v)
    (n l : ℕ) (hl : n + c ≤ l)
    (x : reesAdicProjectiveCechStage (ι := ι) I G l d q)
    (hx : (reesAdicProjectiveCechToModule (ι := ι) I G l d q).hom x = 0) :
    (reesAdicProjectiveCechTransition (ι := ι) I G l n
      ((Nat.le_add_right n c).trans hl) d q).hom x = 0 := by
  let h : n ≤ l := (Nat.le_add_right n c).trans hl
  let z := DirectSum.lof R ℕ
    (fun k ↦ reesAdicProjectiveCechStage (ι := ι) I G k d q) l x
  have hz : z ∈ Submodule.span (reesAlgebra I) s := by
    rw [hspan]
    exact (reesAdicProjectiveCechKernel_lof_mem_iff (ι := ι) I G l d q x).mpr hx
  have hzero := reesAdicProjectiveCechTransitionComponent_zero_of_span
    (ι := ι) I G d q c s hs n l h hl z hz
  change (reesAdicProjectiveCechTransition (ι := ι) I G l n h d q).hom
    ((DirectSum.lof R ℕ
      (fun k ↦ reesAdicProjectiveCechStage (ι := ι) I G k d q) l x) l) = 0 at hzero
  simpa only [DirectSum.lof_apply] using hzero

/-- 実際の Čech 包含の核の遷移は、一様に遅らせれば零になる。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化に用いる核の零化の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechKernel_transition_eventually_zero [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    ∃ c : ℕ, ∀ n l (hl : n + c ≤ l)
      (x : reesAdicProjectiveCechStage (ι := ι) I G l d q),
      (reesAdicProjectiveCechToModule (ι := ι) I G l d q).hom x = 0 →
      (reesAdicProjectiveCechTransition (ι := ι) I G l n
        ((Nat.le_add_right n c).trans hl) d q).hom x = 0 := by
  obtain ⟨c, s, hspan, hs⟩ :=
    reesAdicProjectiveCechKernel_bounded_homogeneous_generators (ι := ι) I G d q
  exact ⟨c, fun n l hl x hx ↦
    reesAdicProjectiveCechKernel_transition_zero_of_bounded_generators
      (ι := ι) I G d q c (↑s : Set _) hspan hs n l hl x hx⟩

end SerrePositivity.AlgebraicGeometry
