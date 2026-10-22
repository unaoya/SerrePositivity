module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionProductJointRealization
public import SerrePositivity.InfinityCategories.F2.Ind.NerveProductSwapIso

/-!
概要：同じ積添字全体の比較を curry し、元の strict 分類像の制限へ戻す。
方針：二つの nerve の積の標準同型と、元の共同実現の評価公式を使う。
規約：値ごとの比較ではなく図式の族全体の関手同型。
使われ方：底の初頂点局所化による大域分類比較の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I J : Type u} [Category.{u} I] [Category.{u} J] {B : SSet.{u}}
  (F : I ⥤ LeftFibrationObject B)

/-- 同じ積添字の共同実現を curry すると、元の Kan 図式値の族の実現を回収する。 -/
lemma sectionProductJointRealization_curry (A : Jᵒᵖ ⥤ Over B) :
    curry ((uliftNerveProductSwapIso I J).inv ≫ sectionProductJointRealization F A) =
      HomotopyLimits.strictCoherentDiagram (strictLeftSectionKanDiagramFamily F A) ≫
        kanDiagramRealization J := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

/-- 元の共同 weighted 分類を、同じ通常の添字の coherent 図式として読む。 -/
def strictLeftWeightedClassification :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj B) :=
  curry ((HomotopyLimits.uliftTensorIso.{u, u + 1} B (nerve I)).inv ≫
    leftStraighteningInfinityDiagram (leftFibrationWeightedProjection F))

/-- 同じ共同分類を初頂点で制限してから curry すると、元の curry した図式の制限になる。 -/
lemma sectionProductClassification_curry :
    curry ((uliftNerveProductSwapIso I (TransportSimplexCategory B)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (sectionProductBaseMap I B) ≫
        leftStraighteningInfinityDiagram (leftFibrationWeightedProjection F)) =
      strictLeftWeightedClassification F ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u} := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_pre_app, strictLeftWeightedClassification,
    uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

/-- 元の共同分類の同じ初頂点制限は、strict 分類像の切断による実現と大域的に同型。 -/
def strictLeftWeightedClassificationSectionIso :
    FunctorIso
      (strictLeftWeightedClassification F ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u})
      (HomotopyLimits.strictCoherentDiagram
        (strictLeftSectionKanDiagramFamily F (transportSimplexDomainFunctor B)) ≫
          kanDiagramRealization (TransportSimplexCategory B)) := by
  have h := ((sectionProductClassificationRealizationIso F).precomp
    (uliftNerveProductSwapIso I (TransportSimplexCategory B)).inv).curry
  rw [sectionProductClassification_curry, sectionProductJointRealization_curry] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Ind
