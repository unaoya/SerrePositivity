module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechIntMaps

/-!
概要：整数係数の Čech H と既存の Rees 表示を、射影と遷移に自然に比較する。
方針：整数への係数制限と、実際の商環の比較の二つを合成する。
規約：原典 Stacks 30.20.4 と BST13 Lemma 3.9 の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
使われ方：2e の核の評価と像の安定化を、Frobenius の有向系の同じ写像へ渡す。
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

/-- 元の Čech H の整数係数表示と、係数環上の表示の加法群同型。 -/
def projectiveCechIntToModuleEquiv (q : ℕ) :
    ProjectiveCechIntHomology (ι := ι) G q ≃+
      reesAdicProjectiveCechTarget (ι := ι) G 0 q :=
  (projectiveCechIntRestrictionHomologyIso
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0) q).toLinearEquiv.toAddEquiv

/-- Rees の閉厚化表示から、実際の商環の Čech H への加法群同型。 -/
def reesClosedCechModuleToRingEquiv (n q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I G n 0 q ≃+
      reesAdicProjectiveCechTarget (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) 0 q :=
  (reesClosedRingCechIso (ι := ι) I G n 0 q).toLinearEquiv.toAddEquiv

/-- 閉厚化の整数係数表示から、同じ商環の係数環上の Čech H への加法群同型。 -/
def reesClosedCechIntToRingEquiv (n q : ℕ) :
    ReesClosedCechIntHomology (ι := ι) I G n q ≃+
      reesAdicProjectiveCechTarget (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) 0 q :=
  (projectiveCechIntRestrictionHomologyIso
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) 0) q).toLinearEquiv.toAddEquiv

/-- 閉厚化の整数係数 Čech H と、既存の Rees の閉厚化の Čech H の加法群同型。 -/
def reesClosedCechIntToModuleEquiv (n q : ℕ) :
    ReesClosedCechIntHomology (ι := ι) I G n q ≃+
      reesAdicProjectiveClosedCechHomology (ι := ι) I G n 0 q :=
  (reesClosedCechIntToRingEquiv (ι := ι) I G n q).trans
    (reesClosedCechModuleToRingEquiv (ι := ι) I G n q).symm

/-- Rees 表示へ戻して環の商の表示へ送ると、整数への係数制限比較になる。 -/
theorem reesClosedCechIntToModuleEquiv_compare (n q : ℕ)
    (x : ReesClosedCechIntHomology (ι := ι) I G n q) :
    reesClosedCechModuleToRingEquiv (ι := ι) I G n q
      (reesClosedCechIntToModuleEquiv (ι := ι) I G n q x) =
    reesClosedCechIntToRingEquiv (ι := ι) I G n q x :=
  (reesClosedCechModuleToRingEquiv (ι := ι) I G n q).apply_symm_apply _

/-- 整数係数の射影は、比較を通すと 2e の Rees の実際の射影になる。 -/
theorem reesClosedCechIntToModuleEquiv_projection (n q : ℕ)
    (x : ProjectiveCechIntHomology (ι := ι) G q) :
    reesClosedCechIntToModuleEquiv (ι := ι) I G n q
      (reesClosedCechIntProjection (ι := ι) I G n q x) =
    (reesAdicProjectiveClosedCechProjection (ι := ι) I G n 0 q).hom
      (projectiveCechIntToModuleEquiv (ι := ι) G q x) := by
  apply (reesClosedCechModuleToRingEquiv (ι := ι) I G n q).injective
  rw [reesClosedCechIntToModuleEquiv_compare]
  have hi := congrArg (fun f ↦ f.hom x)
    (projectiveCechIntRestrictionHomologyIso_naturality
      (reesClosedRingProjectionChartMap (ι := ι) I G n 0) q)
  have hr := congrArg (fun f ↦ f.hom (projectiveCechIntToModuleEquiv (ι := ι) G q x))
    (reesClosedRingCechIso_projection (ι := ι) I G n 0 q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi hr
  exact hi.trans hr.symm

/-- 整数係数の遷移も、比較を通すと 2e の Rees の実際の遷移になる。 -/
theorem reesClosedCechIntToModuleEquiv_transition (n m : ℕ) (hmn : m ≤ n) (q : ℕ)
    (x : ReesClosedCechIntHomology (ι := ι) I G n q) :
    reesClosedCechIntToModuleEquiv (ι := ι) I G m q
      (reesClosedCechIntTransition (ι := ι) I G n m hmn q x) =
    (reesAdicProjectiveClosedCechTransition (ι := ι) I G n m hmn 0 q).hom
      (reesClosedCechIntToModuleEquiv (ι := ι) I G n q x) := by
  apply (reesClosedCechModuleToRingEquiv (ι := ι) I G m q).injective
  rw [reesClosedCechIntToModuleEquiv_compare]
  have hi := congrArg (fun f ↦ f.hom x)
    (projectiveCechIntRestrictionHomologyIso_naturality
      (reesClosedRingTransitionChartMap (ι := ι) I G n m hmn 0) q)
  have hr := congrArg (fun f ↦ f.hom (reesClosedCechIntToModuleEquiv (ι := ι) I G n q x))
    (reesClosedRingCechIso_transition (ι := ι) I G n m hmn 0 q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi hr
  change _ = ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
    (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G n m hmn 0))).hom
    (reesClosedCechModuleToRingEquiv (ι := ι) I G n q
      (reesClosedCechIntToModuleEquiv (ι := ι) I G n q x)) at hr
  rw [reesClosedCechIntToModuleEquiv_compare] at hr
  exact hi.trans hr.symm

/-- 閉厚化間の整数係数の遷移と元の対象からの射影の合成は、浅い段への射影。 -/
theorem reesClosedCechIntTransition_projection (n m : ℕ) (hmn : m ≤ n) (q : ℕ)
    (x : ProjectiveCechIntHomology (ι := ι) G q) :
    reesClosedCechIntTransition (ι := ι) I G n m hmn q
      (reesClosedCechIntProjection (ι := ι) I G n q x) =
    reesClosedCechIntProjection (ι := ι) I G m q x := by
  apply (reesClosedCechIntToModuleEquiv (ι := ι) I G m q).injective
  rw [reesClosedCechIntToModuleEquiv_transition,
    reesClosedCechIntToModuleEquiv_projection, reesClosedCechIntToModuleEquiv_projection]
  exact congrArg (fun f ↦ f.hom (projectiveCechIntToModuleEquiv (ι := ι) G q x))
    (reesAdicProjectiveClosedCechTransition_projection (ι := ι) I G n m hmn 0 q)

end SerrePositivity.AlgebraicGeometry
