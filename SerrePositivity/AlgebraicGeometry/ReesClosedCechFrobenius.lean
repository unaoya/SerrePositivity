module

public import SerrePositivity.AlgebraicGeometry.ReesClosedRingNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusAdic

/-!
概要：実際の商環の Čech Frobenius を、Rees の閉厚化の表示へ戻す。
方針：同じ標準開図式の具体的な比較で共役し、射影の可換性を保存する。
規約：H の I 進商と、閉厚化の H は区別する。
使われ方：閉厚化の互換族と形式関数への Frobenius の接続。
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

/-- 実際の商環の Frobenius を、同じ閉厚化の Rees 表示の Čech H へ戻す。
原典 BS17 Lemma 4.6(i) と BST13 Lemma 3.9(1) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveClosedCechFrobenius (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I G n d q →ₛₗ[frobenius R p]
      reesAdicProjectiveClosedCechHomology (ι := ι) I G n ((p : ℤ) * d) q :=
  ((reesClosedRingCechIso (ι := ι) I G n ((p : ℤ) * d) q).toLinearEquiv.symm.toLinearMap).comp
    ((projectiveNatGradedCechFrobenius (ι := ι) p hp
      (projectiveRingQuotient_primeCast_eq_zero ((I ^ n).map (algebraMap R A)) p hz)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d q).comp
      (reesClosedRingCechIso (ι := ι) I G n d q).toLinearEquiv.toLinearMap)

/-- Rees 表示へ戻した閉厚化の Čech Frobenius は、環の商の表示の写像そのもの。 -/
theorem reesAdicProjectiveClosedCechFrobenius_compare (n : ℕ) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveClosedCechHomology (ι := ι) I G n d q) :
    (reesClosedRingCechIso (ι := ι) I G n ((p : ℤ) * d) q).toLinearEquiv
        (reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz n d q x) =
      projectiveNatGradedCechFrobenius (ι := ι) p hp
        (projectiveRingQuotient_primeCast_eq_zero ((I ^ n).map (algebraMap R A)) p hz)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d q
        ((reesClosedRingCechIso (ι := ι) I G n d q).toLinearEquiv x) :=
  (reesClosedRingCechIso (ι := ι) I G n ((p : ℤ) * d) q).toLinearEquiv.apply_symm_apply _

/-- 実際の閉厚化の Čech Frobenius は、以前からの閉厚化への射影と可換。
原典 BS17 Lemma 4.6(i) の Hⁱ と制限の可換性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechFrobenius_projection (n : ℕ) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveCechTarget (ι := ι) G d q) :
    reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz n d q
        ((reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q).hom x) =
      (reesAdicProjectiveClosedCechProjection (ι := ι) I G n ((p : ℤ) * d) q).hom
        (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q x) := by
  let e := (reesClosedRingCechIso (ι := ι) I G n ((p : ℤ) * d) q).toLinearEquiv
  apply e.injective
  rw [reesAdicProjectiveClosedCechFrobenius_compare]
  have hπ := congrArg (fun f ↦ f.hom x)
    (reesClosedRingCechIso_projection (ι := ι) I G n d q)
  have hπp := congrArg
    (fun f ↦ f.hom (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q x))
    (reesClosedRingCechIso_projection (ι := ι) I G n ((p : ℤ) * d) q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hπ hπp
  exact (congrArg
    (projectiveNatGradedCechFrobenius (ι := ι) p hp
      (projectiveRingQuotient_primeCast_eq_zero ((I ^ n).map (algebraMap R A)) p hz)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d q) hπ).trans
    ((projectiveRingQuotientCechFrobenius_naturality (ι := ι)
      ((I ^ n).map (algebraMap R A)) G p hp hz d q x).trans hπp.symm)

/-- 実際の閉厚化の Čech Frobenius は、以前からの I 進遷移と可換。
原典 Stacks 30.20.4 と BS17 Lemma 4.6(i) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechFrobenius_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveClosedCechHomology (ι := ι) I G i d q) :
    (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h ((p : ℤ) * d) q).hom
        (reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz i d q x) =
      reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz j d q
        ((reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom x) := by
  let ei := (reesClosedRingCechIso (ι := ι) I G i d q).toLinearEquiv
  let ej := (reesClosedRingCechIso (ι := ι) I G j d q).toLinearEquiv
  let eip := (reesClosedRingCechIso (ι := ι) I G i ((p : ℤ) * d) q).toLinearEquiv
  let ejp := (reesClosedRingCechIso (ι := ι) I G j ((p : ℤ) * d) q).toLinearEquiv
  let ti := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
    (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G i j h d))
  let tip := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
    (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G i j h ((p : ℤ) * d)))
  let Fi := projectiveNatGradedCechFrobenius (ι := ι) p hp
    (projectiveRingQuotient_primeCast_eq_zero ((I ^ i).map (algebraMap R A)) p hz)
    (projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G) d q
  let Fj := projectiveNatGradedCechFrobenius (ι := ι) p hp
    (projectiveRingQuotient_primeCast_eq_zero ((I ^ j).map (algebraMap R A)) p hz)
    (projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G) d q
  have ht := congrArg (fun f ↦ f.hom x)
    (reesClosedRingCechIso_transition (ι := ι) I G i j h d q)
  have htp := congrArg
    (fun f ↦ f.hom (reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz i d q x))
    (reesClosedRingCechIso_transition (ι := ι) I G i j h ((p : ℤ) * d) q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ht htp
  have hF : Fj (ti.hom (ei x)) = tip.hom (Fi (ei x)) :=
    projectiveNatGradedCechFrobenius_naturality p hp
      (projectiveRingQuotient_primeCast_eq_zero ((I ^ i).map (algebraMap R A)) p hz)
      (projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)
      (projectiveRingQuotient_primeCast_eq_zero ((I ^ j).map (algebraMap R A)) p hz)
      (projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G)
      (reesClosedRingTransition (ι := ι) I i j h)
      (reesClosedRingTransition_preservesPiece (ι := ι) I G i j h) d q (ei x)
  apply ejp.injective
  calc
    _ = tip.hom
        (eip (reesAdicProjectiveClosedCechFrobenius (ι := ι) I G p hp hz i d q x)) := htp
    _ = tip.hom (Fi (ei x)) := congrArg tip.hom
      (reesAdicProjectiveClosedCechFrobenius_compare (ι := ι) I G p hp hz i d q x)
    _ = Fj (ti.hom (ei x)) := hF.symm
    _ = Fj (ej ((reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom x)) :=
      congrArg Fj ht.symm
    _ = _ := (reesAdicProjectiveClosedCechFrobenius_compare (ι := ι)
      I G p hp hz j d q
      ((reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q).hom x)).symm

end SerrePositivity.AlgebraicGeometry
