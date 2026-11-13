module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechIntThickening
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFrobeniusHomology

/-!
概要：閉厚化への射影・遷移と Frobenius の因子分解を整数係数の Čech H へ送る。
方針：実際の標準開図式にコホモロジー関手を適用する。
規約：BST13 Lemma 3.9 の Hⁱ に対応する Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。
使われ方：2e の評価と実際の Frobenius 有向系を結ぶ。
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

/-- 実際の閉厚化の捻り零の Čech H の整数加群表示。 -/
abbrev ReesClosedCechIntHomology (n q : ℕ) :=
  ProjectiveCechIntHomology (ι := ι)
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) q

/-- 実際の閉厚化への Čech H の射影を整数線形に読む。 -/
def reesClosedCechIntProjection (n q : ℕ) :
    ProjectiveCechIntHomology (ι := ι) G q →ₗ[ℤ] ReesClosedCechIntHomology (ι := ι) I G n q :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
    (fullCechComplexMap (Functor.whiskerRight (reesClosedRingProjectionChartMap (ι := ι) I G n 0)
      (ModuleCat.restrictScalars (Int.castRingHom R))))).hom

/-- 実際の閉厚化間の Čech H の遷移を整数線形に読む。 -/
def reesClosedCechIntTransition (n m : ℕ) (hmn : m ≤ n) (q : ℕ) :
    ReesClosedCechIntHomology (ι := ι) I G n q →ₗ[ℤ]
      ReesClosedCechIntHomology (ι := ι) I G m q :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
    (fullCechComplexMap (Functor.whiskerRight
      (reesClosedRingTransitionChartMap (ι := ι) I G n m hmn 0)
      (ModuleCat.restrictScalars (Int.castRingHom R))))).hom

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 実際の閉厚化を経由する Frobenius の Čech H の整数線形写像。 -/
def reesClosedCechIntThickening (n e q : ℕ) :
    ReesClosedCechIntHomology (ι := ι) I G n q →ₗ[ℤ]
      ReesClosedCechIntHomology (ι := ι) I G (p ^ e * n) q :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
    (fullCechComplexMap (reesClosedCechIntThickeningDiagram (ι := ι) I G p hp hR hA n e))).hom

/-- Čech H で厚化から戻すと、既に構成した反復 Frobenius になる。 -/
theorem reesClosedCechIntThickening_factor (n e q : ℕ) :
    (reesClosedCechIntTransition (ι := ι) I G (p ^ e * n) n
      (Nat.le_mul_of_pos_left n (pow_pos hp.pos e)) q).comp
        (reesClosedCechIntThickening (ι := ι) I G p hp hR hA n e q) =
    projectiveCechIntFrobeniusHomology (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) e q := by
  let H : (Finset ι ⥤ ModuleCat.{u} ℤ) ⥤ ModuleCat.{u} ℤ := fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  have h := congrArg (fun f ↦ (H.map f).hom)
    (reesClosedCechIntThickeningDiagram_factor (ι := ι) I G p hp hR hA n e)
  simp only [H.map_comp, ModuleCat.hom_comp] at h
  exact h

/-- Čech H への射影と、厚化を経由する反復 Frobenius は可換。 -/
theorem reesClosedCechIntThickening_projection (n e q : ℕ) :
    (reesClosedCechIntThickening (ι := ι) I G p hp hR hA n e q).comp
        (reesClosedCechIntProjection (ι := ι) I G n q) =
      (reesClosedCechIntProjection (ι := ι) I G (p ^ e * n) q).comp
        (projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA e q) := by
  let H : (Finset ι ⥤ ModuleCat.{u} ℤ) ⥤ ModuleCat.{u} ℤ := fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  have h := congrArg (fun f ↦ (H.map f).hom)
    (reesClosedCechIntThickeningDiagram_projection (ι := ι) I G p hp hR hA n e)
  simp only [H.map_comp, ModuleCat.hom_comp] at h
  exact h

end SerrePositivity.AlgebraicGeometry
