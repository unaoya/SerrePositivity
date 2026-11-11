module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechStabilization
public import SerrePositivity.AlgebraicGeometry.AdicProjectionCompletionInverse

/-!
概要：実際の射影 Čech コホモロジーに、形式関数の完備化同型を与える。
方針：証明済みの核の評価と像の安定化を、加群の完備化比較へ代入する。
規約：導来関手の Hⁱ とは比較せず、Mathlib の I 進完備化を使う。
使われ方：BST13 Lemma 3.9 の正次数の議論と、BS17 の Čech 降下への入力。
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

/-- 実際の閉厚化の Čech コホモロジーの互換族の加群。 -/
def reesAdicProjectiveClosedCechCompatibleFamilies (d : ℤ) (q : ℕ) :
    Submodule R (∀ n, reesAdicProjectiveClosedCechHomology (ι := ι) I G n d q) :=
  compatibleLinearFamilies
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom)

/-- Iⁿ 倍は、実際の閉厚化への Čech 写像の核に入る。
原典 Stacks 30.20.4(1) の Hⁱ の核に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechProjection_pow_le_ker (n : ℕ) (d : ℤ) (q : ℕ) :
    I ^ n • (⊤ : Submodule R (reesAdicProjectiveCechTarget (ι := ι) G d q)) ≤
      LinearMap.ker (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom := by
  rw [reesAdicProjectiveClosedCechProjection_ker_eq_image]
  exact reesAdicProjectiveCechImage_contains_pow (ι := ι) I G n d q

/-- 閉厚化への Čech 射影の互換性を、線形写像の合成として述べる。 -/
theorem reesAdicProjectiveClosedCechProjection_linear_compat
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom.comp
      (reesAdicProjectiveClosedCechProjection (ι := ι) I G i d q).hom =
    (reesAdicProjectiveClosedCechProjection (ι := ι) I G j d q).hom :=
  congrArg ModuleCat.Hom.hom
    (reesAdicProjectiveClosedCechTransition_projection (ι := ι) I G i j h d q)

/-- 元の Čech コホモロジーの完備化から、実際の閉厚化の互換族への標準写像。 -/
def reesAdicProjectiveClosedCechCompletionMap (d : ℤ) (q : ℕ) :
    AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q) →ₗ[R]
      reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G d q :=
  adicProjectionCompletionMap I
    (fun n ↦ (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom)
    (fun n ↦ reesAdicProjectiveClosedCechProjection_pow_le_ker (ι := ι) I G n d q)
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom)
    (fun i j h ↦ reesAdicProjectiveClosedCechProjection_linear_compat (ι := ι) I G i j h d q)

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) M]

/-- 核の評価を、n+c 段の核が Iⁿ 倍に入るという形にする。
原典 Stacks 30.20.4(1) の Hⁱ の核の評価の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechProjection_shifted_kernel_bound (d : ℤ) (q : ℕ) :
    ∃ c : ℕ, ∀ n,
      LinearMap.ker (reesAdicProjectiveClosedCechProjection (ι := ι) I G (n + c) d q).hom ≤
        I ^ n • (⊤ : Submodule R (reesAdicProjectiveCechTarget (ι := ι) G d q)) := by
  obtain ⟨c, hc⟩ := reesAdicProjectiveClosedCechProjection_kernel_bound (ι := ι) I G d q
  refine ⟨c, fun n ↦ ?_⟩
  simpa only [Nat.add_sub_cancel] using hc (n + c) (Nat.le_add_left c n)

/-- 閉厚化の Čech 互換族の各成分は、元のコホモロジーからの像に入る。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化から得られる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechCompatibleFamilies_mem_range (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G d q) (n : ℕ) :
    x.val n ∈ LinearMap.range
      (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom := by
  obtain ⟨c, hc⟩ := reesAdicProjectiveClosedCechTransition_range_stabilizes (ι := ι) I G d q
  exact compatibleLinearFamilies_mem_range_of_stable
    (fun k ↦ (reesAdicProjectiveClosedCechProjection (ι := ι) I G k d q).hom)
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom)
    (fun k ↦ ⟨k + c, Nat.le_add_right k c, (hc k (k + c) le_rfl).le⟩) x n

/-- 実際の射影 Čech コホモロジーの形式関数の線形同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveClosedCechCompletionLinearEquiv (d : ℤ) (q : ℕ) :
    AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q) ≃ₗ[R]
      reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G d q :=
  let c := (reesAdicProjectiveClosedCechProjection_shifted_kernel_bound (ι := ι) I G d q).choose
  let hker := (reesAdicProjectiveClosedCechProjection_shifted_kernel_bound
    (ι := ι) I G d q).choose_spec
  adicProjectionCompletionLinearEquiv I
    (fun n ↦ (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom) c hker
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom)
    (fun x n ↦ reesAdicProjectiveClosedCechCompatibleFamilies_mem_range (ι := ι) I G d q x n)
    (fun i j h ↦ reesAdicProjectiveClosedCechProjection_linear_compat (ι := ι) I G i j h d q)
    (fun n ↦ reesAdicProjectiveClosedCechProjection_pow_le_ker (ι := ι) I G n d q)

/-- 形式関数の Čech 同型の順写像は、標準写像そのもの。 -/
@[simp] theorem reesAdicProjectiveClosedCechCompletionLinearEquiv_toLinearMap (d : ℤ) (q : ℕ) :
    (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G d q).toLinearMap =
      reesAdicProjectiveClosedCechCompletionMap (ι := ι) I G d q := rfl

/-- 形式関数の Čech 同型を加群の元で評価すると、元の閉厚化への射影になる。 -/
@[simp] theorem reesAdicProjectiveClosedCechCompletionLinearEquiv_of_apply
    (d : ℤ) (q : ℕ) (m : reesAdicProjectiveCechTarget (ι := ι) G d q) (n : ℕ) :
    (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G d q
      (AdicCompletion.of I _ m)).val n =
      (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom m := rfl

end SerrePositivity.AlgebraicGeometry
