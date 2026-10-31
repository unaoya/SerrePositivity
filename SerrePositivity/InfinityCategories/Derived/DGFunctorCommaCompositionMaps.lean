module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionCompositionMaps
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaComparison
public import SerrePositivity.InfinityCategories.Derived.EnrichedCompositionBoundary
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
/-!
概要：commaの全 Hom tensor から、実入力・比較対象の合成とその実比較差を構成する。
方針：既存の eComp と二射影を使い、元の同じ dg 関手の合成保存を保持する。
規約：全 Hom 複体をパラメータとする。使われ方：comma dg 圏の実合成の二射影。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F)
/-- 全 Hom tensor 上の、元の実入力の合成。 -/
def dgFunctorCommaSourceComposite :
    dgFunctorCommaHomComplex R C E F X Y ⊗
      dgFunctorCommaHomComplex R C E F Y Z ⟶ homObject R C X.source Z.source :=
  (dgFunctorCommaSourceHomMap R C E F X Y ⊗ₘ
    dgFunctorCommaSourceHomMap R C E F Y Z) ≫
      eComp (Complex R) X.source Y.source Z.source
/-- 同じ全 Hom tensor 上の、実比較対象の合成。 -/
def dgFunctorCommaReplacementComposite :
    dgFunctorCommaHomComplex R C E F X Y ⊗
      dgFunctorCommaHomComplex R C E F Y Z ⟶
        homObject R E X.replacement Z.replacement :=
  (dgFunctorCommaReplacementHomMap R C E F X Y ⊗ₘ
    dgFunctorCommaReplacementHomMap R C E F Y Z) ≫
      eComp (Complex R) X.replacement Y.replacement Z.replacement
/-- 合成入力の実像は、同じ dg 関手の二実像の合成と厳密に一致する。 -/
lemma dgFunctorCommaSourceComposite_image :
    dgFunctorCommaSourceComposite R C E F X Y Z ≫ F.map X.source Z.source =
      (dgFunctorCommaImageHomMap R C E F X Y ⊗ₘ
        dgFunctorCommaImageHomMap R C E F Y Z) ≫
          eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) := by
  dsimp only [dgFunctorCommaSourceComposite, dgFunctorCommaImageHomMap]
  rw [Category.assoc, F.map_comp, ← Category.assoc, tensorHom_comp_tensorHom]
/-- 全 Hom tensor 上の、二実合成の比較差。 -/
def dgFunctorCommaCompositeBoundary :=
  biprod.lift (dgFunctorCommaSourceComposite R C E F X Y Z)
    (dgFunctorCommaReplacementComposite R C E F X Y Z) ≫
      dgFunctorCommaDifference R C E F X Z
/-- 比較差を、元の実合成と出力の実合成の差へ厳密に展開する。 -/
lemma dgFunctorCommaCompositeBoundary_eq :
    dgFunctorCommaCompositeBoundary R C E F X Y Z =
      (dgFunctorCommaImageHomMap R C E F X Y ⊗ₘ
        dgFunctorCommaImageHomMap R C E F Y Z) ≫
          eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) ≫
          eHomWhiskerRight (Complex R) X.augmentation
            (ForgetEnrichment.of (Complex R) (F.obj Z.source)) -
      dgFunctorCommaReplacementComposite R C E F X Y Z ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
          Z.augmentation := by
  have h := parameterBiprod_lift_difference
    (dgFunctorCommaSourceComposite R C E F X Y Z)
    (dgFunctorCommaReplacementComposite R C E F X Y Z)
    (F.map X.source Z.source ≫ eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj Z.source)))
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
      Z.augmentation)
  have he : dgFunctorCommaCompositeBoundary R C E F X Y Z =
      (dgFunctorCommaSourceComposite R C E F X Y Z ≫ F.map X.source Z.source) ≫
        eHomWhiskerRight (Complex R) X.augmentation
          (ForgetEnrichment.of (Complex R) (F.obj Z.source)) -
      dgFunctorCommaReplacementComposite R C E F X Y Z ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
          Z.augmentation := by
    simpa only [dgFunctorCommaCompositeBoundary, dgFunctorCommaDifference,
      Category.assoc] using! h
  rw [he, dgFunctorCommaSourceComposite_image, Category.assoc]
end SerrePositivity.InfinityCategories
