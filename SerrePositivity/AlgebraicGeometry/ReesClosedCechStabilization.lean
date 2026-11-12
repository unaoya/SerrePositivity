module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechTransition
public import SerrePositivity.AlgebraicGeometry.ReesCechKernelVanishing
public import SerrePositivity.AlgebraicGeometry.ProjectiveFormalFunctionsBounds

/-!
概要：実際の I 進閉厚化の Čech コホモロジーの像が安定することを示す。
方針：長完全列の自然性と、次の次数での包含の核の一様零化を合わせる。
規約：基底の Noether 性と加群の多項式環上の有限生成性を仮定する。
使われ方：射影 Čech 版の形式関数の完備化比較への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 次の次数の Čech 核が遷移で零になれば、実際の閉厚化の像は元の像に一致。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化に用いる Čech 版の図式追跡。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechTransition_range_eq_of_kernel_killed
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ)
    (hkill : ∀ x : reesAdicProjectiveCechStage (ι := ι) I G i d (q + 1),
      (reesAdicProjectiveCechToModule (ι := ι) I G i d (q + 1)).hom x = 0 →
        (reesAdicProjectiveCechTransition (ι := ι) I G i j h d (q + 1)).hom x = 0) :
    LinearMap.range (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom =
      LinearMap.range (reesAdicProjectiveClosedCechProjection (ι := ι) I G j d q).hom := by
  apply formalFunctions_range_eq_of_kernel_killed
    (reesAdicProjectiveClosedCechProjection (ι := ι) I G j d q).hom
    (reesAdicProjectiveClosedCechProjection (ι := ι) I G i d q).hom
    (reesAdicProjectiveClosedCechConnecting (ι := ι) I G j d q).hom
    (reesAdicProjectiveClosedCechConnecting (ι := ι) I G i d q).hom
    (reesAdicProjectiveCechToModule (ι := ι) I G i d (q + 1)).hom
    (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom
    (reesAdicProjectiveCechTransition (ι := ι) I G i j h d (q + 1)).hom
  · exact reesAdicProjectiveClosedCech_exact_projection_connecting (ι := ι) I G j d q
  · exact reesAdicProjectiveClosedCech_exact_connecting_inclusion (ι := ι) I G i d q
  · exact congrArg ModuleCat.Hom.hom
      (reesAdicProjectiveClosedCechTransition_projection (ι := ι) I G i j h d q)
  · exact congrArg ModuleCat.Hom.hom
      (reesAdicProjectiveClosedCechTransition_connecting (ι := ι) I G i j h d q)
  · intro x hx
    exact hkill x hx

/-- 実際の閉厚化の Čech コホモロジーの像は、一様に遅らせれば安定する。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechTransition_range_stabilizes [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    ∃ c : ℕ, ∀ n l (hl : n + c ≤ l),
      LinearMap.range (reesAdicProjectiveClosedCechTransition (ι := ι) I G l n
        ((Nat.le_add_right n c).trans hl) d q).hom =
      LinearMap.range (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom := by
  obtain ⟨c, hc⟩ := reesAdicProjectiveCechKernel_transition_eventually_zero
    (ι := ι) I G d (q + 1)
  refine ⟨c, ?_⟩
  intro n l hl
  exact reesAdicProjectiveClosedCechTransition_range_eq_of_kernel_killed
    (ι := ι) I G l n ((Nat.le_add_right n c).trans hl) d q (hc n l hl)

end SerrePositivity.AlgebraicGeometry
