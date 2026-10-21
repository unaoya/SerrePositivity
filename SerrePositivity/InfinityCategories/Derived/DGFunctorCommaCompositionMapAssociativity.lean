module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaAssociativityMaps
/-!
概要：比較 cochain を後合成する実二作用の三つの結合式を証明する。
方針：実入力像・実比較対象の合成保存と、全パラメータ豊穣結合律を使う。
使われ方：comma dg 圏の結合律の三つの比較項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 実合成の入力像は、実入力像同士の豊穣合成。 -/
lemma dgFunctorCommaComposition_image
    (X Y Z : DGFunctorCommaObject R C E F) :
    dgFunctorCommaComposition R C E F X Y Z ≫
      dgFunctorCommaImageHomMap R C E F X Z =
    (dgFunctorCommaImageHomMap R C E F X Y ⊗ₘ
      dgFunctorCommaImageHomMap R C E F Y Z) ≫
        eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) := by
  rw [dgFunctorCommaImageHomMap, ← Category.assoc,
    dgFunctorCommaComposition_source, dgFunctorCommaSourceComposite_image]
variable (W X Y Z : DGFunctorCommaObject R C E F)
/-- 第一比較項を輸送する実作用の結合式。 -/
lemma dgFunctorCommaFirstCompositionMap_assoc :
    dgFunctorCommaFirstCompositionMap R C E F W X Y ▷
        dgFunctorCommaHomComplex R C E F Y Z ≫
      dgFunctorCommaFirstCompositionMap R C E F W Y Z =
    (α_ (homObject R E W.replacement (F.obj X.source))
      (dgFunctorCommaHomComplex R C E F X Y)
      (dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
      (homObject R E W.replacement (F.obj X.source)) ◁
        dgFunctorCommaComposition R C E F X Y Z ≫
          dgFunctorCommaFirstCompositionMap R C E F W X Z := by
  simp only [dgFunctorCommaFirstCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    dgFunctorCommaComposition_image]
  exact parameterEnriched_associativity (Complex R) E
    W.replacement (F.obj X.source) (F.obj Y.source) (F.obj Z.source) (𝟙 _)
    (dgFunctorCommaImageHomMap R C E F X Y)
    (dgFunctorCommaImageHomMap R C E F Y Z)
/-- 中央比較項を輸送する、第一・第二実作用の混合結合式。 -/
lemma dgFunctorCommaMixedCompositionMap_assoc :
    dgFunctorCommaSecondCompositionMap R C E F W X Y ▷
        dgFunctorCommaHomComplex R C E F Y Z ≫
      dgFunctorCommaFirstCompositionMap R C E F W Y Z =
    (α_ (dgFunctorCommaHomComplex R C E F W X)
      (homObject R E X.replacement (F.obj Y.source))
      (dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
      dgFunctorCommaHomComplex R C E F W X ◁
        dgFunctorCommaFirstCompositionMap R C E F X Y Z ≫
          dgFunctorCommaSecondCompositionMap R C E F W X Z := by
  simp only [dgFunctorCommaFirstCompositionMap,
    dgFunctorCommaSecondCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  exact parameterEnriched_associativity (Complex R) E
    W.replacement X.replacement (F.obj Y.source) (F.obj Z.source)
    (dgFunctorCommaReplacementHomMap R C E F W X) (𝟙 _)
    (dgFunctorCommaImageHomMap R C E F Y Z)
/-- 第三比較項を輸送する実作用の結合式。 -/
lemma dgFunctorCommaSecondCompositionMap_assoc :
    dgFunctorCommaComposition R C E F W X Y ▷
        (homObject R E Y.replacement (F.obj Z.source)) ≫
      dgFunctorCommaSecondCompositionMap R C E F W Y Z =
    (α_ (dgFunctorCommaHomComplex R C E F W X)
      (dgFunctorCommaHomComplex R C E F X Y)
      (homObject R E Y.replacement (F.obj Z.source))).hom ≫
      dgFunctorCommaHomComplex R C E F W X ◁
        dgFunctorCommaSecondCompositionMap R C E F X Y Z ≫
          dgFunctorCommaSecondCompositionMap R C E F W X Z := by
  simp only [dgFunctorCommaSecondCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    dgFunctorCommaComposition_replacement,
    dgFunctorCommaReplacementComposite]
  exact parameterEnriched_associativity (Complex R) E
    W.replacement X.replacement Y.replacement (F.obj Z.source)
    (dgFunctorCommaReplacementHomMap R C E F W X)
    (dgFunctorCommaReplacementHomMap R C E F X Y) (𝟙 _)
end SerrePositivity.InfinityCategories
