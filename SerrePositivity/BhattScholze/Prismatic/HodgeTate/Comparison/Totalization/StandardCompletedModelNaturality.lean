module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.StandardCompletedModelComparison

/-!
# 標準 S 完備比較の図式と模型の射についての自然性

## 概要
元の図式の射と指定分解の可換な射を、同じ標準比較へ渡す。

## 方針
完備化前の実際の四角形を証明し、元の標準単位の普遍性で延長する。

## 規約
模型間の射やその可換性を存在から仮定せず、実際の射を引数にする。

## 使われ方
BS 著者版 Lemma 4.22 の比較射の自然性と模型の照合。
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

/-- 同じ各行の係数拡大と完備化を、図式の射へ施す関手。 -/
abbrev standardCompletedRowsFunctor (f : R →+* S) {r : ℕ} (x : Fin r → R) :
    CochainComplex (Complex R) ℕ ⥤ CochainComplex (Complex S) ℕ :=
  baseChangeRowsFunctor f ⋙ (finiteCompletionFunctor (fun j => f (x j))).mapHomologicalComplex (.up ℕ)

/-- 元の完備化前の標準射は、指定された実際の可換な模型の射について自然である。 -/
@[reassoc] theorem baseChangeModelToCompletedRows_naturality (f : R →+* S) {r : ℕ} (x : Fin r → R)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M)
    {P Q : Complex R} (q : P ⟶ total K) (q' : Q ⟶ total M) (h : P ⟶ Q)
    (comm : q ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g = h ≫ q') :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h ≫
        baseChangeModelToCompletedRows f x M q' =
      baseChangeModelToCompletedRows f x K q ≫
        (cochainProductTotalizationFunctor (ModuleCat.{u} S)).map ((standardCompletedRowsFunctor f x).map g) := by
  have hc := congrArg ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map comm
  simp only [Functor.map_comp] at hc
  have hn := congrArg (cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
    (finiteCompletionRowsUnit_naturality (fun j => f (x j)) ((baseChangeRowsFunctor f).map g))
  simp only [Functor.map_comp] at hn
  dsimp only [baseChangeModelToCompletedRows]
  rw [← Category.assoc, ← hc]
  simp only [Category.assoc]
  rw [baseChangeTotalComparison_naturality_assoc, hn]
  simp only [standardCompletedRowsFunctor, Functor.comp_map, Category.assoc]

/-- 元の標準単位による完備延長も、同じ可換な模型の射について自然である。 -/
@[reassoc] theorem finiteCompletedBaseChangeModelComparison_naturality
    (f : R →+* S) {r : ℕ} (x : Fin r → R)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M)
    {P Q : Complex R} (q : P ⟶ total K) (q' : Q ⟶ total M) (h : P ⟶ Q)
    (comm : q ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g = h ≫ q') :
    DerivedCategory.Q.map ((finiteCompletionFunctor (fun j => f (x j))).map
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h)) ≫
        finiteCompletedBaseChangeModelComparison f x M q' =
      finiteCompletedBaseChangeModelComparison f x K q ≫ DerivedCategory.Q.map
        ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map ((standardCompletedRowsFunctor f x).map g)) := by
  apply finiteCompletionHom_ext (fun j => f (x j)) (baseChange f P)
    (DerivedCategory.Q.obj (total (standardCompletedBaseChangeRows f x M)))
    (total_finiteCompletedRows_isComplete (fun j => f (x j)) ((baseChangeRowsFunctor f).obj M))
  have hu := congrArg DerivedCategory.Q.map
    (finiteCompletionUnit_naturality (fun j => f (x j))
      (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map h))
  simp only [Functor.map_comp] at hu
  rw [← Category.assoc, ← hu]
  simp only [Category.assoc]
  rw [unit_comp_finiteCompletedBaseChangeModelComparison, unit_comp_finiteCompletedBaseChangeModelComparison_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (baseChangeModelToCompletedRows_naturality f x g q q' h comm)

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
