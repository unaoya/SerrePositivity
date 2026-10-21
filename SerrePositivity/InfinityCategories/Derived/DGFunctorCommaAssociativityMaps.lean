module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaUnitLaws
public import SerrePositivity.InfinityCategories.Derived.EnrichedParameterizedAssociativity
/-!
概要：commaの二つの三重合成を構成し、実入力と比較対象への射影を比較する。
方針：全 Hom tensor の結合子と、元・出力の実豊穣結合律を使う。
規約：比較 cochain の照合は別工程。使われ方：comma dg 圏の結合律。
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
  (W X Y Z : DGFunctorCommaObject R C E F)
/-- 左の実二合成を先に行う、同じ全三重 Hom からの鎖写像。 -/
def dgFunctorCommaLeftAssociatedComposition :=
  dgFunctorCommaComposition R C E F W X Y ▷
    dgFunctorCommaHomComplex R C E F Y Z ≫
      dgFunctorCommaComposition R C E F W Y Z
/-- 右の実二合成を先に行い、同じ全三重 Hom から括弧変更する鎖写像。 -/
def dgFunctorCommaRightAssociatedComposition :=
  (α_ (dgFunctorCommaHomComplex R C E F W X)
    (dgFunctorCommaHomComplex R C E F X Y)
    (dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
    dgFunctorCommaHomComplex R C E F W X ◁
      dgFunctorCommaComposition R C E F X Y Z ≫
        dgFunctorCommaComposition R C E F W X Z
/-- 二つの実三重合成の入力 Hom 射影は、同じ豊穣結合律で一致。 -/
lemma dgFunctorComma_associativity_source :
    dgFunctorCommaLeftAssociatedComposition R C E F W X Y Z ≫
      dgFunctorCommaSourceHomMap R C E F W Z =
    dgFunctorCommaRightAssociatedComposition R C E F W X Y Z ≫
      dgFunctorCommaSourceHomMap R C E F W Z := by
  simp only [dgFunctorCommaLeftAssociatedComposition,
    dgFunctorCommaRightAssociatedComposition, Category.assoc,
    dgFunctorCommaComposition_source, dgFunctorCommaSourceComposite,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  exact parameterEnriched_associativity (Complex R) C W.source X.source Y.source Z.source
    (dgFunctorCommaSourceHomMap R C E F W X)
    (dgFunctorCommaSourceHomMap R C E F X Y)
    (dgFunctorCommaSourceHomMap R C E F Y Z)
/-- 二つの実三重合成の比較対象 Hom 射影も、同じ豊穣結合律で一致。 -/
lemma dgFunctorComma_associativity_replacement :
    dgFunctorCommaLeftAssociatedComposition R C E F W X Y Z ≫
      dgFunctorCommaReplacementHomMap R C E F W Z =
    dgFunctorCommaRightAssociatedComposition R C E F W X Y Z ≫
      dgFunctorCommaReplacementHomMap R C E F W Z := by
  simp only [dgFunctorCommaLeftAssociatedComposition,
    dgFunctorCommaRightAssociatedComposition, Category.assoc,
    dgFunctorCommaComposition_replacement,
    dgFunctorCommaReplacementComposite,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  exact parameterEnriched_associativity (Complex R) E
    W.replacement X.replacement Y.replacement Z.replacement
    (dgFunctorCommaReplacementHomMap R C E F W X)
    (dgFunctorCommaReplacementHomMap R C E F X Y)
    (dgFunctorCommaReplacementHomMap R C E F Y Z)
end SerrePositivity.InfinityCategories
