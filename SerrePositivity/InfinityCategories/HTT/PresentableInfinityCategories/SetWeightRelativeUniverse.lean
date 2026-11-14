module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightElementsRelativeNaturality
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsPrefixFactorization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverUniverseNaturality

/-!
概要：元の小さい相対切断表示と、元の大きい unstraightening への相対写像空間を比較する。
方針：相対関手空間の ULift 同型と、標的の元の縮小同型を順に使う。
規約：始域の要素の圏とその射影を固定し、全空間の同型を新しく選ばない。
使われ方：G8 の四角形①で、構成した相対自然性を元の切断同値に接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] (X : I ⥤ Type u)
  (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u})

/-- 元の要素の圏を始域に固定した、相対関手空間の大小の比較同型。 -/
def setWeightRelativeUniverseIso :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (relativeFunctorSpace (smallLeftUnstraighteningProjection G) (SetWeight.projection X)) ≅
    relativeFunctorSpace (leftUnstraighteningProjection G)
      ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X)) :=
  uliftRelativeFunctorIso (smallLeftUnstraighteningProjection G) (SetWeight.projection X) ≪≫
    relativeFunctorOverIso
      (Iso.refl (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X))))
      (smallLeftUnstraighteningOverIso G)

/-- 元の小さい要素の圏の比較による前合成は、同じ大小の表示変更と厳密に可換。 -/
lemma setWeightRelativeUniverse_pre :
    (SSet.uliftFunctor.{u + 1, u}).map
      (relativeFunctorOverPre (smallLeftUnstraighteningProjection G)
        (show Over.mk (SetWeight.projection X) ⟶
            Over.mk (smallLeftUnstraighteningProjection (spaceDiagram X)) from
          Over.homMk (SetWeight.elementsComparisonNatural X)
            (SetWeight.elementsComparisonNatural_projection X))) ≫
      (setWeightRelativeUniverseIso X G).hom =
    (smallLeftUnstraighteningRelativeFunctorIso (spaceDiagram X) G).hom ≫
      relativeFunctorOverPre (leftUnstraighteningProjection G)
        (show Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (SetWeight.projection X)) ⟶
            Over.mk (leftUnstraighteningProjection (spaceDiagram X)) from
          Over.homMk (setWeightElementsUnstraightening X)
            (setWeightElementsUnstraightening_projection X)) := by
  simp only [setWeightRelativeUniverseIso, smallLeftUnstraighteningRelativeFunctorIso,
    Iso.trans_hom, Category.assoc]
  change _ ≫ uliftRelativeFunctorMap _ _ ≫ _ = uliftRelativeFunctorMap _ _ ≫ _
  rw [← Category.assoc, uliftRelativeFunctorMap_overPre, Category.assoc]
  erw [relativeFunctorOverIso_pre_hom _ (smallLeftUnstraighteningOverIso (spaceDiagram X))
      (smallLeftUnstraighteningOverIso G)]
  rfl

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
