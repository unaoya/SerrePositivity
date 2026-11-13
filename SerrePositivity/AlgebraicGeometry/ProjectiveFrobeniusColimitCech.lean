module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntSequential
public import SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusFunctor

/-!
概要：実際の標準開の Frobenius 係数順極限から Čech 複体と閉厚化の制限を作る。
方針：係数系の余極限を先に取り、既存の全タプル複体を適用する。
規約：I 進完備化ではなく Frobenius の順極限を用いる。
使われ方：F6 の正次数と F7 の次数零を、F8 が使う同じ複体の射にまとめる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [DirectSum.Decomposition G]
variable [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 実際の標準開係数の Frobenius 順極限から作る Čech 複体。 -/
def projectiveFrobeniusColimitCechComplex : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  fullCechComplex (colimit (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA))

/-- 閉厚化への実際の制限を係数の Frobenius 順極限の Čech 複体へ移す。 -/
def reesClosedFrobeniusColimitCechMap (I : Ideal R) (n : ℕ) :
    projectiveFrobeniusColimitCechComplex (ι := ι) G p hp hR hA ⟶
      projectiveFrobeniusColimitCechComplex (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) :=
  fullCechComplexMap (colim.map
    (reesClosedFrobeniusCoefficientNatTrans (ι := ι) I G p hp hR hA n))

/-- 同じ閉厚化の複体の射が誘導する各次数の Čech H の写像。 -/
def reesClosedFrobeniusColimitCechHomologyMap (I : Ideal R) (n q : ℕ) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
    (reesClosedFrobeniusColimitCechMap (ι := ι) G p hp hR hA I n)).hom

/-- この複体の Čech H と各段の Čech H の順極限の同型。
BST13 Lemma 3.9 の Hⁱ に用いる Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
def projectiveFrobeniusColimitCechHomologyIso (q : ℕ) :
    (projectiveFrobeniusColimitCechComplex (ι := ι) G p hp hR hA).homology q ≅
      colimit (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA ⋙
        fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) :=
  projectiveIntCechSequentialHomologyIso
    (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA) q

end SerrePositivity.AlgebraicGeometry
