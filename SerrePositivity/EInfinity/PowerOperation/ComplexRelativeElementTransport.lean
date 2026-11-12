module

public import SerrePositivity.EInfinity.PowerOperation.NerveColumnRoofConjugation
public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementDerivedRoofComparison

/-!
# 指定比較と指定 sourceIso で運んだ実全屋根族

DAG XIII §2.2 の native な降下の補助。元の全 pinched 族の像の両端を、
指定 sourceIso の同じ頂点成分で運び、元の通常導来屋根へ照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.FrameHom SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors (pinchedHomMap)
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors
open AdjointFunctorsBetweenInfinityCategories (intervalFamilyHom)
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

/-- 同じ指定 sourceIso の頂点成分を使う両端の輸送。 -/
def complexRelativeElementEndpointEquivalence :=
  pinchedEndpointEquivalence
    (functorIsoEvaluate (complexHammockDerivedComparison_sourceIso A)
      (ComposableArrows.mk₀ ((complexRelativeUp A).obj X)))
    (functorIsoEvaluate (complexHammockDerivedComparison_sourceIso A)
      (ComposableArrows.mk₀ ((complexRelativeUp A).obj Y)))

/-- 指定比較による全族の像を、同じ sourceIso で元の導来源の頂点へ運ぶ。 -/
def complexRelativeElementDerivedPinchedMap :=
  complexRelativeElementHammockPinchedMap A X Y ≫
    pinchedHomMap (complexHammockDerivedComparison A) _ _ ≫
      (complexRelativeElementEndpointEquivalence A X Y).hom

lemma complexRelativeElementDerivedPinchedMap_roof_arrow :
    Arrow.mk (intervalFamilyHom
      (complexRelativeElementDerivedPinchedMap A X Y ≫
        MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
      Arrow.mk ((complexRelativeElementDerivedAugmentationIso A X Y).inv ≫
        NerveColumn.hom (complexRelativeDerivedSource A)
          (complexRelativeElementEvaluation A X Y)) := by
  let V := complexRelativeElementColumn A X Y
  let p := complexRelativeElementAugmentation A X Y
  let s := complexRelativeElementEvaluation A X Y
  let hp := complexRelativeElementAugmentation_weak A X Y
  let K := complexHammockDerivedComparison A
  let e := complexHammockDerivedComparison_sourceIso A
  let f := complexRelativeElementHammockPinchedMap A X Y ≫ pinchedHomMap K _ _
  have ht := pinchedEndpointEquivalence_family
    (functorIsoEvaluate e (ComposableArrows.mk₀ ((complexRelativeUp A).obj X)))
    (functorIsoEvaluate e (ComposableArrows.mk₀ ((complexRelativeUp A).obj Y))) f
  have hn := nerveColumnRoofConjugation_arrow e V p
    (RoofPrefix.postcomp_augmentation_invertible (complexRelativeCategory A) V p hp K)
    (complexRelativeElementDerivedAugmentation_invertible A X Y) s f
    (complexRelativeElementPinchedFamily_comparison_arrow A X Y)
  exact (congrArg Arrow.mk ht).trans hn

end SerrePositivity.EInfinity.PowerOperation
