module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionUnitLaws
public import SerrePositivity.InfinityCategories.Derived.EnrichedParameterizedAssociativity
/-!
概要：出力分解の二つの三重合成を構成し、実入力と半自由出力への射影を比較する。
方針：全 Hom tensor の結合子と、元・出力の実豊穣結合律を使う。
規約：比較 cochain の照合は別工程。使われ方：分解 dg 圏の結合律。
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
  (W X Y Z : DGModuleFunctorResolutionObject R C E F)
/-- 左の実二合成を先に行う、同じ全三重 Hom からの鎖写像。 -/
def dgModuleFunctorResolutionLeftAssociatedComposition :=
  dgModuleFunctorResolutionComposition R C E F W X Y ▷
    dgModuleFunctorResolutionHomComplex R C E F Y Z ≫
      dgModuleFunctorResolutionComposition R C E F W Y Z
/-- 右の実二合成を先に行い、同じ全三重 Hom から括弧変更する鎖写像。 -/
def dgModuleFunctorResolutionRightAssociatedComposition :=
  (α_ (dgModuleFunctorResolutionHomComplex R C E F W X)
    (dgModuleFunctorResolutionHomComplex R C E F X Y)
    (dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom ≫
    dgModuleFunctorResolutionHomComplex R C E F W X ◁
      dgModuleFunctorResolutionComposition R C E F X Y Z ≫
        dgModuleFunctorResolutionComposition R C E F W X Z
/-- 二つの実三重合成の入力 Hom 射影は、同じ豊穣結合律で一致。 -/
lemma dgModuleFunctorResolution_associativity_source :
    dgModuleFunctorResolutionLeftAssociatedComposition R C E F W X Y Z ≫
      dgModuleFunctorResolutionSourceHomMap R C E F W Z =
    dgModuleFunctorResolutionRightAssociatedComposition R C E F W X Y Z ≫
      dgModuleFunctorResolutionSourceHomMap R C E F W Z := by
  simp only [dgModuleFunctorResolutionLeftAssociatedComposition,
    dgModuleFunctorResolutionRightAssociatedComposition, Category.assoc,
    dgModuleFunctorResolutionComposition_source, dgModuleFunctorResolutionSourceComposite,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  exact parameterEnriched_associativity (Complex R) C W.source X.source Y.source Z.source
    (dgModuleFunctorResolutionSourceHomMap R C E F W X)
    (dgModuleFunctorResolutionSourceHomMap R C E F X Y)
    (dgModuleFunctorResolutionSourceHomMap R C E F Y Z)
/-- 二つの実三重合成の半自由出力 Hom 射影も、同じ豊穣結合律で一致。 -/
lemma dgModuleFunctorResolution_associativity_replacement :
    dgModuleFunctorResolutionLeftAssociatedComposition R C E F W X Y Z ≫
      dgModuleFunctorResolutionReplacementHomMap R C E F W Z =
    dgModuleFunctorResolutionRightAssociatedComposition R C E F W X Y Z ≫
      dgModuleFunctorResolutionReplacementHomMap R C E F W Z := by
  simp only [dgModuleFunctorResolutionLeftAssociatedComposition,
    dgModuleFunctorResolutionRightAssociatedComposition, Category.assoc,
    dgModuleFunctorResolutionComposition_replacement,
    dgModuleFunctorResolutionReplacementComposite,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  exact parameterEnriched_associativity (Complex R) (RightModule R E)
    W.replacement.val X.replacement.val Y.replacement.val Z.replacement.val
    (dgModuleFunctorResolutionReplacementHomMap R C E F W X)
    (dgModuleFunctorResolutionReplacementHomMap R C E F X Y)
    (dgModuleFunctorResolutionReplacementHomMap R C E F Y Z)
end SerrePositivity.InfinityCategories
