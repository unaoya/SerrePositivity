module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementColumn
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixColumnRoof

/-!
# 指定比較関手で運ぶ同じ全要素屋根の pinched 族

DAG XIII §2.2 の native な降下への前段。比較関手と指定 sourceIso を保ち、
全パラメータ付きの屋根を既存の複体の導来源へ照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.SimplicialLocalization SerrePositivity.EInfinity.FrameHom
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open MorphismSpaces.Basic (pinchedHom)
open FullFaithfulAndEssentiallySurjectiveFunctors (pinchedHomMap)
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors
open AdjointFunctorsBetweenInfinityCategories (intervalFamilyHom)
open SerrePositivity.InfinityCategories.Project.DerivedCategories (derivedInfinityCategory)
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def complexRelativeElementHammockPinchedMap :
    nerve (complexRelativeElementIndex A X Y) ⟶
      pinchedHom
        ((complexHammockSource A).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ ((complexRelativeUp A).obj X)))
        ((complexHammockSource A).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ ((complexRelativeUp A).obj Y))) :=
  RoofPrefix.familyMap (complexRelativeCategory A) (complexRelativeElementColumn A X Y)
    (complexRelativeElementAugmentation A X Y) (complexRelativeElementAugmentation_weak A X Y)
    (complexRelativeElementEvaluation A X Y)
    (fun f => complexRelativeElementColumn_map_weak A X Y f) ≫
      kanHammockHomPinchedMap (complexRelativeCategory A)
        ((complexRelativeUp A).obj X) ((complexRelativeUp A).obj Y)

/-- 指定比較による全 pinched 族の像は、同じ通常列の augmentation の逆と評価。 -/
lemma complexRelativeElementPinchedFamily_comparison_arrow :
    let C := complexRelativeCategory A
    let V := complexRelativeElementColumn A X Y
    let p := complexRelativeElementAugmentation A X Y
    let hp := complexRelativeElementAugmentation_weak A X Y
    let s := complexRelativeElementEvaluation A X Y
    let F := complexHammockDerivedComparison A
    Arrow.mk (intervalFamilyHom
      (complexRelativeElementHammockPinchedMap A X Y ≫ pinchedHomMap F _ _ ≫
        MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
      Arrow.mk ((NerveColumn.augmentationIso (complexHammockSource A ≫ F) V p
        (RoofPrefix.postcomp_augmentation_invertible C V p hp F)).inv ≫
          NerveColumn.hom (complexHammockSource A ≫ F) s) :=
  RoofPrefix.native_family_postcomp_column_roof_arrow (complexRelativeCategory A)
    (complexRelativeElementColumn A X Y) (complexRelativeElementAugmentation A X Y)
    (complexRelativeElementAugmentation_weak A X Y) (complexRelativeElementEvaluation A X Y)
    (fun f => complexRelativeElementColumn_map_weak A X Y f) (complexHammockDerivedComparison A)

end SerrePositivity.EInfinity.PowerOperation
