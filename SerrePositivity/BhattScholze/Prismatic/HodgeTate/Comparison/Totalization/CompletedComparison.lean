module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TotalCompleteness
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletionAdditive
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction

/-!
# 完備化後の標準テンソル–Tot 比較

## 概要
元の標準鎖写像と完備化の単位から、同じ完備化と同じ積全複体の間の導来射を作る。

## 方針
標的の完備性により標準単位だけを反転する。擬同型性はこの定義には含めない。

## 規約
行ごとの完備化も始域の完備化も、既存の complexCompletionFunctor を使う。

## 使われ方
BS 著者版 Lemma 4.22 の標準比較。有限切断と尾部の評価による同値性の証明に用いる。
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
variable {R : Type u} [CommRing R]

/-- 完備な標的への元の射を、標準単位に沿って延長する指定射。 -/
def completionToComplete (a : R) {X Y : Complex R} (f : X ⟶ Y)
    (hY : IsComplete R a (DerivedCategory.Q.obj Y)) :
    complexCompletionObject R a X ⟶ DerivedCategory.Q.obj Y :=
  DerivedCategory.Q.map ((complexCompletionFunctor R a).map f) ≫
    (complexCompletionUnitIso R a Y hY).inv

/-- この延長の標準単位との合成は、元の射そのものである。 -/
@[reassoc] theorem unit_comp_completionToComplete (a : R) {X Y : Complex R} (f : X ⟶ Y)
    (hY : IsComplete R a (DerivedCategory.Q.obj Y)) :
    DerivedCategory.Q.map (complexCompletionUnit R a X) ≫ completionToComplete a f hY =
      DerivedCategory.Q.map f := by
  have hn := congrArg DerivedCategory.Q.map (complexCompletionUnit_naturality R a f)
  simp only [Functor.map_comp] at hn
  dsimp only [completionToComplete]
  rw [← Category.assoc, ← hn, Category.assoc]
  change DerivedCategory.Q.map f ≫
    (complexCompletionUnitIso R a Y hY).hom ≫ (complexCompletionUnitIso R a Y hY).inv = _
  rw [Iso.hom_inv_id, Category.comp_id]

/-- 行ごとの主元完備化。元の余鎖図式と標準微分を保つ。 -/
def completedRows (a : R) (K : CochainComplex (Complex R) ℕ) :
    CochainComplex (Complex R) ℕ :=
  ((complexCompletionFunctor R a).mapHomologicalComplex (.up ℕ)).obj K

/-- 各行の元の標準単位からなる余鎖図式の射。 -/
def completionRowsUnit (a : R) (K : CochainComplex (Complex R) ℕ) :
    K ⟶ completedRows a K where
  f n := complexCompletionUnit R a (K.X n)
  comm' i j _ := (complexCompletionUnit_naturality R a (K.d i j)).symm

/-- 完備化後の各行の積全複体は、同じ主元について導来完備。 -/
theorem total_completedRows_isComplete (a : R) (K : CochainComplex (Complex R) ℕ) :
    IsComplete R a (DerivedCategory.Q.obj (total (completedRows a K))) :=
  total_isComplete a (completedRows a K)
    (fun n => complexCompletionObject_isComplete R a (K.X n))

/-- 完備化前のテンソル–Tot 比較と、各行の標準単位との合成。 -/
def tensorToCompletedRows (a : R) (L : Complex R) (K : CochainComplex (Complex R) ℕ) :
    cochainTensor L (total K) ⟶ total (completedRows a (tensorRows L K)) :=
  tensorTotalComparison L K ≫
    (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (completionRowsUnit a (tensorRows L K))

/-- 標的の標準単位だけを反転して得る、完備化後の標準比較。 -/
def completedTensorTotalComparison (a : R) (L : Complex R)
    (K : CochainComplex (Complex R) ℕ) :
    complexCompletionObject R a (cochainTensor L (total K)) ⟶
      DerivedCategory.Q.obj (total (completedRows a (tensorRows L K))) :=
  completionToComplete a (tensorToCompletedRows a L K)
    (total_completedRows_isComplete a (tensorRows L K))

/-- 完備化後の比較は、元の比較と各行の単位から指定されている。 -/
@[reassoc] theorem unit_comp_completedTensorTotalComparison (a : R) (L : Complex R)
    (K : CochainComplex (Complex R) ℕ) :
    DerivedCategory.Q.map (complexCompletionUnit R a (cochainTensor L (total K))) ≫
        completedTensorTotalComparison a L K =
      DerivedCategory.Q.map (tensorToCompletedRows a L K) :=
  unit_comp_completionToComplete a _ _

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
