module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechThickeningFrobenius
public import SerrePositivity.AlgebraicGeometry.ReesClosedLocalizedThickeningNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSemilinearNaturality

/-!
概要：閉厚化を経由する反復 Frobenius と厚化間の遷移の Čech 比較。
方針：局所化で確かめた四角形を標準開図式へ制限し、半線形 H の自然性を適用する。
規約：商の H を使い、H 自身の商とは同一視しない。
使われ方：2e の像の安定化を Frobenius 順極限へ渡す。
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
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 厚化 Frobenius と遷移の四角形は実際の標準開図式で可換。 -/
theorem reesClosedChartThickeningFrobeniusNatTrans_transition
    (n m e : ℕ) (hmn : m ≤ n) (d : ℤ) :
    reesClosedRingTransitionChartMap (ι := ι) I G n m hmn d ≫
        reesClosedChartThickeningFrobeniusNatTrans I G p hp hR hA m e d =
    reesClosedChartThickeningFrobeniusNatTrans I G p hp hR hA n e d ≫
      Functor.whiskerRight
        (reesClosedRingTransitionChartMap (ι := ι) I G (p ^ e * n) (p ^ e * m)
          (Nat.mul_le_mul_left (p ^ e) hmn) (((p ^ e : ℕ) : ℤ) * d))
        (ModuleCat.restrictScalars (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact reesClosedLocalizedThickeningFrobenius_transition I p hp hR hA
    (projectiveLaurentDenominator R T) n m e hmn z.val

/-- 閉厚化の Čech H の厚化 Frobenius は厚さを下げる遷移と可換。
BST13 Lemma 3.9(1) と BS17 Lemma 4.6(i) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedCechThickeningFrobenius_transition
    (n m e : ℕ) (hmn : m ≤ n) (d : ℤ) (q : ℕ)
    (x : (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d)).homology q) :
    reesClosedCechThickeningFrobenius I G p hp hR hA m e d q
      (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G n m hmn d))).hom x) =
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
      (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G
        (p ^ e * n) (p ^ e * m) (Nat.mul_le_mul_left (p ^ e) hmn)
        (((p ^ e : ℕ) : ℤ) * d)))).hom
      (reesClosedCechThickeningFrobenius I G p hp hR hA n e d q x) :=
  projectiveCechSemilinearHomologyMap_naturality
    (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
    (reesClosedChartThickeningFrobeniusNatTrans I G p hp hR hA n e d)
    (reesClosedChartThickeningFrobeniusNatTrans I G p hp hR hA m e d)
    _ _ (reesClosedChartThickeningFrobeniusNatTrans_transition I G p hp hR hA n m e hmn d) q x

end SerrePositivity.AlgebraicGeometry
