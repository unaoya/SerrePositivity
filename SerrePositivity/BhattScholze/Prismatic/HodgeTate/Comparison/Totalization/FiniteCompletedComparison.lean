module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionReflection
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TotalCompleteness

/-!
# 有限列の完備化後の標準テンソル–Tot 比較

## 概要
同じ指定積全複体と、本体の主元完備化を反復した模型の間に標準比較を指定する。

## 方針
元のテンソル比較と各行の合成単位を使い、全座標に完備な標的への一意な延長を取る。

## 規約
擬同型性はこの定義には仮定しない。比較は元の標準単位で一意に指定する。

## 使われ方
BS 著者版 Lemma 4.22 の有限生成イデアルについての比較。
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

/-- 各行に同じ有限反復完備化を施す。 -/
def finiteCompletedRows {r : ℕ} (x : Fin r → R) (K : CochainComplex (Complex R) ℕ) :
    CochainComplex (Complex R) ℕ :=
  ((finiteCompletionFunctor x).mapHomologicalComplex (.up ℕ)).obj K

/-- 各行の元の合成単位からなる余鎖図式の射。 -/
def finiteCompletionRowsUnit {r : ℕ} (x : Fin r → R) (K : CochainComplex (Complex R) ℕ) :
    K ⟶ finiteCompletedRows x K where
  f n := finiteCompletionUnit x (K.X n)
  comm' i j _ := (finiteCompletionUnit_naturality x (K.d i j)).symm

/-- 行の合成単位は、元の余鎖図式について自然である。 -/
@[reassoc] theorem finiteCompletionRowsUnit_naturality {r : ℕ} (x : Fin r → R)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    g ≫ finiteCompletionRowsUnit x M = finiteCompletionRowsUnit x K ≫
      ((finiteCompletionFunctor x).mapHomologicalComplex (.up ℕ)).map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact finiteCompletionUnit_naturality x (g.f n)

/-- 各行を完備化した指定 Tot は、列の各元について完備である。 -/
theorem total_finiteCompletedRows_isComplete {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) (j : Fin r) :
    IsComplete R (x j) (DerivedCategory.Q.obj (total (finiteCompletedRows x K))) :=
  total_isComplete (x j) (finiteCompletedRows x K)
    (fun n => finiteCompletion_isComplete x (K.X n) j)

/-- 元の標準テンソル比較と、各行の元の合成単位との合成。 -/
def tensorToFiniteCompletedRows {r : ℕ} (x : Fin r → R) (L : Complex R)
    (K : CochainComplex (Complex R) ℕ) :
    cochainTensor L (total K) ⟶ total (finiteCompletedRows x (tensorRows L K)) :=
  tensorTotalComparison L K ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
    (finiteCompletionRowsUnit x (tensorRows L K))

/-- 完備化前からの元の射は、図式について自然である。 -/
@[reassoc] theorem tensorToFiniteCompletedRows_naturality {r : ℕ} (x : Fin r → R)
    (L : Complex R) {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    cochainTensorMap (𝟙 L) ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g) ≫
        tensorToFiniteCompletedRows x L M =
      tensorToFiniteCompletedRows x L K ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (((finiteCompletionFunctor x).mapHomologicalComplex (.up ℕ)).map
          (((cochainTensorFixedLeft L).mapHomologicalComplex (.up ℕ)).map g)) := by
  dsimp only [tensorToFiniteCompletedRows]
  rw [← Category.assoc, tensorTotalComparison_naturality, Category.assoc,
    ← Functor.map_comp, finiteCompletionRowsUnit_naturality, Functor.map_comp]
  simp only [Category.assoc]

/-- 有限列の標準単位に沿う一意な延長による、完備化後の比較。 -/
def finiteCompletedTensorTotalComparison {r : ℕ} (x : Fin r → R) (L : Complex R)
    (K : CochainComplex (Complex R) ℕ) :
    DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj (cochainTensor L (total K))) ⟶
      DerivedCategory.Q.obj (total (finiteCompletedRows x (tensorRows L K))) :=
  (finiteCompletionHomEquiv x (cochainTensor L (total K))
    (DerivedCategory.Q.obj (total (finiteCompletedRows x (tensorRows L K))))
    (total_finiteCompletedRows_isComplete x (tensorRows L K))).symm
      (DerivedCategory.Q.map (tensorToFiniteCompletedRows x L K))

/-- 完備比較は、元の合成単位との合成で元の射に戻る。 -/
@[reassoc] theorem unit_comp_finiteCompletedTensorTotalComparison {r : ℕ} (x : Fin r → R)
    (L : Complex R) (K : CochainComplex (Complex R) ℕ) :
    DerivedCategory.Q.map (finiteCompletionUnit x (cochainTensor L (total K))) ≫
        finiteCompletedTensorTotalComparison x L K =
      DerivedCategory.Q.map (tensorToFiniteCompletedRows x L K) := by
  have h := (finiteCompletionHomEquiv x (cochainTensor L (total K))
    (DerivedCategory.Q.obj (total (finiteCompletedRows x (tensorRows L K))))
    (total_finiteCompletedRows_isComplete x (tensorRows L K))).apply_symm_apply
      (DerivedCategory.Q.map (tensorToFiniteCompletedRows x L K))
  simpa only [finiteCompletionHomEquiv_apply, finiteCompletedTensorTotalComparison] using h

/-- 標準単位に沿って指定した完備比較は、元の余鎖図式について自然である。 -/
@[reassoc] theorem finiteCompletedTensorTotalComparison_naturality {r : ℕ} (x : Fin r → R)
    (L : Complex R) {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    finiteCompletedTensorTotalComparison x L K ≫ DerivedCategory.Q.map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (((finiteCompletionFunctor x).mapHomologicalComplex (.up ℕ)).map
          (((cochainTensorFixedLeft L).mapHomologicalComplex (.up ℕ)).map g))) =
      DerivedCategory.Q.map ((finiteCompletionFunctor x).map
        (cochainTensorMap (𝟙 L) ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g))) ≫
          finiteCompletedTensorTotalComparison x L M := by
  apply finiteCompletionHom_ext x (cochainTensor L (total K))
    (DerivedCategory.Q.obj (total (finiteCompletedRows x (tensorRows L M))))
    (total_finiteCompletedRows_isComplete x (tensorRows L M))
  rw [unit_comp_finiteCompletedTensorTotalComparison_assoc]
  have hn := congrArg DerivedCategory.Q.map (finiteCompletionUnit_naturality x
    (cochainTensorMap (𝟙 L) ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g)))
  simp only [Functor.map_comp] at hn
  conv_rhs =>
    rw [← Category.assoc, ← hn, Category.assoc, unit_comp_finiteCompletedTensorTotalComparison]
  simpa only [Functor.map_comp] using
    (congrArg DerivedCategory.Q.map (tensorToFiniteCompletedRows_naturality x L g)).symm

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
