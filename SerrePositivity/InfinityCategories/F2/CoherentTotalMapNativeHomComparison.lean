module

public import SerrePositivity.InfinityCategories.F2.CoherentTotalMapNativeActionComponents
public import SerrePositivity.InfinityCategories.F2.FullyFaithfulComparisonSquare

/-!
概要：元の native 余錐の全 Hom 比較を、指定 native 表現の比較を反映する関手として保持する。
方針：元の余極限性・余錐比較の同値性・縮小同型を同じ順で合成する。
規約：全 Hom と元の図式を保持。使われ方：指定比較の正方形 hu の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})

/-- 元の二 native 頂点間の全 Hom を、元の大きい全空間の関手空間へ写す指定比較。 -/
def coherentTotalMapNativeHomComparison :=
  (coconePointHomFamily (coherentDiagramTotalCocone F) (coherentDiagramTotalVertex G) ≫
    coherentCoconeTotalComparison F (coherentDiagramTotalVertex G)) ≫
      (smallUnstraighteningHomIso F (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).inv

/-- 元の全 Hom 比較の充満忠実性は、元の native 余極限性から従う。 -/
lemma coherentTotalMapNativeHomComparison_isFullyFaithful :
    IsFullyFaithful (coherentTotalMapNativeHomComparison F G) := by
  have h := (coconePointHomFamily_homotopyEquivalence (coherentDiagramTotalCocone F)
    (coherentDiagramTotalCocone_isColimit F) (coherentDiagramTotalVertex G)).isQCatEquivalence
  have hs := (qCatEquivalenceOfIso (smallUnstraighteningHomIso F
    (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).symm).isQCatEquivalence
  exact ((h.comp (coherentCoconeTotalComparison_isQCatEquivalence F
    (coherentDiagramTotalVertex G))).comp hs).isFullyFaithful

end SerrePositivity.InfinityCategories.F2
