module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechFrobenius
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechCompletion
public import SerrePositivity.AlgebraicGeometry.AdicProjectionSemilinearNaturality

/-!
概要：実際の閉厚化の Čech Frobenius を互換族と形式関数の同型に接続する。
方針：射影と I 進遷移の可換性を、既存の半線形な完備化比較へ渡す。
規約：H/IⁿH と閉厚化の H は、標準射影を介して比較する。
使われ方：BST13 Lemma 3.9 と BS17 の Čech 降下の正次数の議論。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable [LinearOrder ι] [Fintype ι]
variable (I : Ideal R) (G : ℕ → Submodule R A) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedMonoid G]
variable (p : ℕ) (hp : p.Prime) [ExpChar R p] (hz : (p : A) = 0)

/-- 閉厚化の Čech Frobenius と I 進遷移の可換式を、半線形写像の等式で述べる。 -/
theorem reesAdicProjectiveClosedCechFrobenius_linear_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h ((p : ℤ) * d) q).hom.comp
        (reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz i d q) =
      (reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz j d q).comp
        (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom := by
  apply LinearMap.ext
  intro x
  exact reesAdicProjectiveClosedCechFrobenius_transition (ι := ι) I G p hp hz i j h d q x

/-- 実際の閉厚化の互換族へ誘導した Čech Frobenius。
原典 Stacks 30.20.4 と BS17 Lemma 4.6(i) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveClosedCechFamiliesFrobenius (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G d q →ₛₗ[frobenius R p]
      reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G ((p : ℤ) * d) q :=
  compatibleSemilinearFamiliesMap (frobenius R p)
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom)
    (fun i j h ↦
      (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h ((p : ℤ) * d) q).hom)
    (fun n ↦ reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz n d q)
    (fun i j h ↦
      reesAdicProjectiveClosedCechFrobenius_linear_transition (ι := ι) I G p hp hz i j h d q)

/-- 互換族の Frobenius は、各厚化の実際の Čech Frobenius を成分ごとに適用する。 -/
@[simp] theorem reesAdicProjectiveClosedCechFamiliesFrobenius_apply (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G d q) (n : ℕ) :
    (reesAdicProjectiveClosedCechFamiliesFrobenius (ι := ι) I G p hp hz d q x).val n =
      reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz n d q (x.val n) := rfl

/-- 閉厚化の Frobenius と元の H の Frobenius の射影の可換式。 -/
theorem reesAdicProjectiveClosedCechFrobenius_linear_projection (n : ℕ) (d : ℤ) (q : ℕ) :
    (reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz n d q).comp
        (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom =
      (reesAdicProjectiveClosedCechProjection (ι := ι) I G n ((p : ℤ) * d) q).hom.comp
        (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q) := by
  apply LinearMap.ext
  intro x
  exact reesAdicProjectiveClosedCechFrobenius_projection (ι := ι) I G p hp hz n d q x

/-- 標準の完備化比較は、実際の閉厚化の互換族の Čech Frobenius と可換。
原典 Stacks 30.20.4–30.20.5 と BS17 Lemma 4.6(i) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechCompletionMap_frobenius (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q)) :
    reesAdicProjectiveClosedCechFamiliesFrobenius (ι := ι) I G p hp hz d q
        (reesAdicProjectiveClosedCechCompletionMap (ι := ι) I G d q a) =
      reesAdicProjectiveClosedCechCompletionMap (ι := ι) I G ((p : ℤ) * d) q
        (projectiveNatGradedCechFrobeniusAdicCompletionMap (ι := ι) I p hp hz G d q a) :=
  adicProjectionCompletionMap_semilinear_naturality_apply I I
    (fun n ↦ (reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom)
    (fun n ↦ (reesAdicProjectiveClosedCechProjection (ι := ι) I G n ((p : ℤ) * d) q).hom)
    (fun n ↦ reesAdicProjectiveClosedCechProjection_pow_le_ker (ι := ι) I G n d q)
    (fun n ↦
      reesAdicProjectiveClosedCechProjection_pow_le_ker (ι := ι) I G n ((p : ℤ) * d) q)
    (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q)
    (fun n ↦ reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz n d q)
    (fun n ↦ adicSemilinear_smul_top_le_comap I I
      (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q)
      (frobeniusIdeal_map_le_self I p) n)
    (fun n ↦
      reesAdicProjectiveClosedCechFrobenius_linear_projection (ι := ι) I G p hp hz n d q)
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom)
    (fun i j h ↦
      (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h ((p : ℤ) * d) q).hom)
    (fun i j h ↦ reesAdicProjectiveClosedCechProjection_linear_compat (ι := ι) I G i j h d q)
    (fun i j h ↦
      reesAdicProjectiveClosedCechProjection_linear_compat (ι := ι) I G i j h ((p : ℤ) * d) q)
    (fun i j h ↦
      reesAdicProjectiveClosedCechFrobenius_linear_transition (ι := ι) I G p hp hz i j h d q) a

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]

/-- 射影版の形式関数の同型は、実際の Čech Frobenius と可換。
原典 Stacks 30.20.5 と BS17 Lemma 4.6(i) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechCompletionLinearEquiv_frobenius (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q)) :
    reesAdicProjectiveClosedCechFamiliesFrobenius (ι := ι) I G p hp hz d q
        (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G d q a) =
      reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G ((p : ℤ) * d) q
        (projectiveNatGradedCechFrobeniusAdicCompletionMap (ι := ι) I p hp hz G d q a) :=
  reesAdicProjectiveClosedCechCompletionMap_frobenius (ι := ι) I G p hp hz d q a

end SerrePositivity.AlgebraicGeometry
