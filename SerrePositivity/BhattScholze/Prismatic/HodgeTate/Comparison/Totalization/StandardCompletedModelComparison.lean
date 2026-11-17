module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalNaturality
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletedComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletedScalarModels

/-!
# 指定模型から通常の行底変換の完備 Tot への標準比較

## 概要
Tot の指定した分解上で通常の S 係数拡大を行い、元の標準比較を S 上で完備化する。

## 方針
係数拡大の元の鎖写像と各行の元の合成単位を使い、完備な標的への一意な延長を取る。

## 規約
分解の射を明示する。この定義だけで通常の行底変換が導来底変換を計算するとは主張しない。

## 使われ方
BS 著者版 Lemma 4.22 の指定 S 線形模型と元の標準比較の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 通常の各行の係数拡大に、同じ像の有限列の完備化を施す。 -/
abbrev standardCompletedBaseChangeRows (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) : CochainComplex (Complex S) ℕ :=
  finiteCompletedRows (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K)

/-- 指定した分解の射、通常の標準比較、元の行の単位からなる S 線形の射。 -/
def baseChangeModelToCompletedRows (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P : Complex R} (q : P ⟶ total K) :
    baseChange f P ⟶ total (standardCompletedBaseChangeRows f x K) :=
  ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q ≫
    baseChangeTotalComparison f K ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
      (finiteCompletionRowsUnit (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))

/-- 標準単位への一意な延長で指定する、S 線形の模型比較。 -/
def finiteCompletedBaseChangeModelComparison (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P : Complex R} (q : P ⟶ total K) :
    DerivedCategory.Q.obj ((finiteCompletionFunctor (fun j => f (x j))).obj (baseChange f P)) ⟶
      DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x K)) :=
  (finiteCompletionHomEquiv (fun j => f (x j)) (baseChange f P)
    (DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x K)))
    (total_finiteCompletedRows_isComplete (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))).symm
      (DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K q))

/-- 指定した標準比較は、元の単位との合成で元の S 線形の射に戻る。 -/
@[reassoc] theorem unit_comp_finiteCompletedBaseChangeModelComparison
    (f : R →+* S) {r : ℕ} (x : Fin r → R) (K : CochainComplex (Complex R) ℕ)
    {P : Complex R} (q : P ⟶ total K) :
    DerivedCategory.Q.map (finiteCompletionUnit (fun j => f (x j)) (baseChange f P)) ≫
        finiteCompletedBaseChangeModelComparison f x K q =
      DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K q) := by
  have h := (finiteCompletionHomEquiv (fun j => f (x j)) (baseChange f P)
    (DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x K)))
    (total_finiteCompletedRows_isComplete (fun j => f (x j)) ((baseChangeRowsFunctor f).obj K))).apply_symm_apply
      (DerivedCategory.Q.map (baseChangeModelToCompletedRows f x K q))
  simpa only [finiteCompletionHomEquiv_apply, finiteCompletedBaseChangeModelComparison] using h

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
