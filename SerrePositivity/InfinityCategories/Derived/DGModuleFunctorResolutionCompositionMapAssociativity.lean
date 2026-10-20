module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionAssociativityMaps
/-!
概要：比較 cochain を後合成する実二作用の三つの結合式を証明する。
方針：実入力像・実半自由出力の合成保存と、全パラメータ豊穣結合律を使う。
使われ方：分解 dg 圏の結合律の三つの比較項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 実合成の入力像は、実入力像同士の豊穣合成。 -/
lemma dgModuleFunctorResolutionComposition_image
    (X Y Z : DGModuleFunctorResolutionObject R C E F) :
    dgModuleFunctorResolutionComposition R C E F X Y Z ≫
      dgModuleFunctorResolutionImageHomMap R C E F X Z =
    (dgModuleFunctorResolutionImageHomMap R C E F X Y ⊗ₘ
      dgModuleFunctorResolutionImageHomMap R C E F Y Z) ≫
        eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) := by
  rw [dgModuleFunctorResolutionImageHomMap, ← Category.assoc,
    dgModuleFunctorResolutionComposition_source, dgModuleFunctorResolutionSourceComposite_image]
variable (W X Y Z : DGModuleFunctorResolutionObject R C E F)
/-- 第一比較項を輸送する実作用の結合式。 -/
lemma dgModuleFunctorResolutionFirstCompositionMap_assoc :
    dgModuleFunctorResolutionFirstCompositionMap R C E F W X Y ▷
        dgModuleFunctorResolutionHomComplex R C E F Y Z ≫
      dgModuleFunctorResolutionFirstCompositionMap R C E F W Y Z =
    (α_ (moduleHom R E W.replacement.val (F.obj X.source))
      (dgModuleFunctorResolutionHomComplex R C E F X Y)
      (dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom ≫
      (moduleHom R E W.replacement.val (F.obj X.source)) ◁
        dgModuleFunctorResolutionComposition R C E F X Y Z ≫
          dgModuleFunctorResolutionFirstCompositionMap R C E F W X Z := by
  simp only [dgModuleFunctorResolutionFirstCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    dgModuleFunctorResolutionComposition_image]
  exact parameterEnriched_associativity (Complex R) (RightModule R E)
    W.replacement.val (F.obj X.source) (F.obj Y.source) (F.obj Z.source) (𝟙 _)
    (dgModuleFunctorResolutionImageHomMap R C E F X Y)
    (dgModuleFunctorResolutionImageHomMap R C E F Y Z)
/-- 中央比較項を輸送する、第一・第二実作用の混合結合式。 -/
lemma dgModuleFunctorResolutionMixedCompositionMap_assoc :
    dgModuleFunctorResolutionSecondCompositionMap R C E F W X Y ▷
        dgModuleFunctorResolutionHomComplex R C E F Y Z ≫
      dgModuleFunctorResolutionFirstCompositionMap R C E F W Y Z =
    (α_ (dgModuleFunctorResolutionHomComplex R C E F W X)
      (moduleHom R E X.replacement.val (F.obj Y.source))
      (dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom ≫
      dgModuleFunctorResolutionHomComplex R C E F W X ◁
        dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z ≫
          dgModuleFunctorResolutionSecondCompositionMap R C E F W X Z := by
  simp only [dgModuleFunctorResolutionFirstCompositionMap,
    dgModuleFunctorResolutionSecondCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  exact parameterEnriched_associativity (Complex R) (RightModule R E)
    W.replacement.val X.replacement.val (F.obj Y.source) (F.obj Z.source)
    (dgModuleFunctorResolutionReplacementHomMap R C E F W X) (𝟙 _)
    (dgModuleFunctorResolutionImageHomMap R C E F Y Z)
/-- 第三比較項を輸送する実作用の結合式。 -/
lemma dgModuleFunctorResolutionSecondCompositionMap_assoc :
    dgModuleFunctorResolutionComposition R C E F W X Y ▷
        (moduleHom R E Y.replacement.val (F.obj Z.source)) ≫
      dgModuleFunctorResolutionSecondCompositionMap R C E F W Y Z =
    (α_ (dgModuleFunctorResolutionHomComplex R C E F W X)
      (dgModuleFunctorResolutionHomComplex R C E F X Y)
      (moduleHom R E Y.replacement.val (F.obj Z.source))).hom ≫
      dgModuleFunctorResolutionHomComplex R C E F W X ◁
        dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z ≫
          dgModuleFunctorResolutionSecondCompositionMap R C E F W X Z := by
  simp only [dgModuleFunctorResolutionSecondCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    dgModuleFunctorResolutionComposition_replacement,
    dgModuleFunctorResolutionReplacementComposite]
  exact parameterEnriched_associativity (Complex R) (RightModule R E)
    W.replacement.val X.replacement.val Y.replacement.val (F.obj Z.source)
    (dgModuleFunctorResolutionReplacementHomMap R C E F W X)
    (dgModuleFunctorResolutionReplacementHomMap R C E F X Y) (𝟙 _)
end SerrePositivity.InfinityCategories
