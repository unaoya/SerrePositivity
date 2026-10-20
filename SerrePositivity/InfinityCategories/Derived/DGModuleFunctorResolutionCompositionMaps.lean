module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionComparison
public import SerrePositivity.InfinityCategories.Derived.EnrichedCompositionBoundary
public import SerrePositivity.HomologicalAlgebra.CochainTensorLinear
/-!
概要：出力分解の全 Hom tensor から、実入力・半自由出力の合成とその実比較差を構成する。
方針：既存の eComp と二射影を使い、元の同じ dg 関手の合成保存を保持する。
規約：全 Hom 複体をパラメータとする。使われ方：分解 dg 圏の実合成の二射影。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
/-- 実二射の持ち上げと実二差の合成は、同じ二つの実合成の差。 -/
lemma parameterBiprod_lift_difference {V : Type u} [Category.{v} V] [Preadditive V]
    {P Q K T : V} [HasBinaryBiproduct P Q] (f : K ⟶ P) (g : K ⟶ Q)
    (a : P ⟶ T) (b : Q ⟶ T) :
    biprod.lift f g ≫ (biprod.fst ≫ a - biprod.snd ≫ b) = f ≫ a - g ≫ b := by
  rw [Preadditive.comp_sub, ← Category.assoc, biprod.lift_fst,
    ← Category.assoc, biprod.lift_snd]
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X Y Z : DGModuleFunctorResolutionObject R C E F)
/-- 全 Hom tensor 上の、元の実入力の合成。 -/
def dgModuleFunctorResolutionSourceComposite :
    dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
      dgModuleFunctorResolutionHomComplex R C E F Y Z ⟶ homObject R C X.source Z.source :=
  (dgModuleFunctorResolutionSourceHomMap R C E F X Y ⊗ₘ
    dgModuleFunctorResolutionSourceHomMap R C E F Y Z) ≫
      eComp (Complex R) X.source Y.source Z.source
/-- 同じ全 Hom tensor 上の、実半自由出力の合成。 -/
def dgModuleFunctorResolutionReplacementComposite :
    dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
      dgModuleFunctorResolutionHomComplex R C E F Y Z ⟶
        moduleHom R E X.replacement.val Z.replacement.val :=
  (dgModuleFunctorResolutionReplacementHomMap R C E F X Y ⊗ₘ
    dgModuleFunctorResolutionReplacementHomMap R C E F Y Z) ≫
      eComp (Complex R) X.replacement.val Y.replacement.val Z.replacement.val
/-- 合成入力の実像は、同じ dg 関手の二実像の合成と厳密に一致する。 -/
lemma dgModuleFunctorResolutionSourceComposite_image :
    dgModuleFunctorResolutionSourceComposite R C E F X Y Z ≫ F.map X.source Z.source =
      (dgModuleFunctorResolutionImageHomMap R C E F X Y ⊗ₘ
        dgModuleFunctorResolutionImageHomMap R C E F Y Z) ≫
          eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) := by
  dsimp only [dgModuleFunctorResolutionSourceComposite, dgModuleFunctorResolutionImageHomMap]
  rw [Category.assoc, F.map_comp, ← Category.assoc, tensorHom_comp_tensorHom]
/-- 全 Hom tensor 上の、二実合成の比較差。 -/
def dgModuleFunctorResolutionCompositeBoundary :=
  biprod.lift (dgModuleFunctorResolutionSourceComposite R C E F X Y Z)
    (dgModuleFunctorResolutionReplacementComposite R C E F X Y Z) ≫
      dgModuleFunctorResolutionDifference R C E F X Z
/-- 比較差を、元の実合成と出力の実合成の差へ厳密に展開する。 -/
lemma dgModuleFunctorResolutionCompositeBoundary_eq :
    dgModuleFunctorResolutionCompositeBoundary R C E F X Y Z =
      (dgModuleFunctorResolutionImageHomMap R C E F X Y ⊗ₘ
        dgModuleFunctorResolutionImageHomMap R C E F Y Z) ≫
          eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) ≫
          eHomWhiskerRight (Complex R) X.augmentation
            (ForgetEnrichment.of (Complex R) (F.obj Z.source)) -
      dgModuleFunctorResolutionReplacementComposite R C E F X Y Z ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement.val)
          Z.augmentation := by
  have h := parameterBiprod_lift_difference
    (dgModuleFunctorResolutionSourceComposite R C E F X Y Z)
    (dgModuleFunctorResolutionReplacementComposite R C E F X Y Z)
    (F.map X.source Z.source ≫ eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj Z.source)))
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement.val)
      Z.augmentation)
  have he : dgModuleFunctorResolutionCompositeBoundary R C E F X Y Z =
      (dgModuleFunctorResolutionSourceComposite R C E F X Y Z ≫ F.map X.source Z.source) ≫
        eHomWhiskerRight (Complex R) X.augmentation
          (ForgetEnrichment.of (Complex R) (F.obj Z.source)) -
      dgModuleFunctorResolutionReplacementComposite R C E F X Y Z ≫
        eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement.val)
          Z.augmentation := by
    simpa only [dgModuleFunctorResolutionCompositeBoundary, dgModuleFunctorResolutionDifference,
      Category.assoc] using! h
  rw [he, dgModuleFunctorResolutionSourceComposite_image, Category.assoc]
end SerrePositivity.InfinityCategories
