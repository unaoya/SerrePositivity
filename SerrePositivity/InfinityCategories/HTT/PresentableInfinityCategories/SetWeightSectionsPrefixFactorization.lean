module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality

/-!
概要：元の切断同値の順射を、元の相対写像空間の比較と切断表示へ分解する。
方針：sectionsEquivalenceNatural と同じ底変換同型を、同じ順で使う。
規約：既存の比較の選択と順射を変更しない。
使われ方：G8 の四角形①で、相対自然性を元の切断同値の全族へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] (X : I ⥤ Type u)
  (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u})

/-- 元の切断同値で使われる、相対関手空間から小さい切断への同じ同型。 -/
def setWeightRelativeSectionsIso :
    relativeFunctorSpace (smallLeftUnstraighteningProjection G) (SetWeight.projection X) ≅
      simplicialSections (smallLeftUnstraighteningProjection (SetWeight.diagram X G)) :=
  let q := smallLeftUnstraighteningProjection G
  let p := SetWeight.projection X
  let q' := smallLeftUnstraighteningProjection (SetWeight.diagram X G)
  let bp : Over.mk q' ≅ Over.mk (pullback.snd q p) :=
    Over.isoMk (smallLeftUnstraighteningBaseChangeIso G p)
      (smallLeftUnstraighteningBaseChangeIso_hom_snd G p)
  (pullbackSectionsRelativeIso q p).symm ≪≫ simplicialSectionsRelativeIso _ ≪≫
    relativeFunctorOverIso (Iso.refl (Over.mk (𝟙 _))) bp.symm ≪≫
      (simplicialSectionsRelativeIso q').symm

/-- 元の切断同値の順射は、同じ実写像と底変換同型の合成そのものである。 -/
lemma setWeightSectionsEquivalenceNatural_hom_factor :
    (SetWeight.sectionsEquivalenceNatural X G).hom =
      leftUnstraighteningPinchedMappingSpaceMap (spaceDiagram X) G ≫
        (smallLeftUnstraighteningRelativeFunctorIso (spaceDiagram X) G).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            (relativeFunctorOverPre (smallLeftUnstraighteningProjection G)
              (show Over.mk (SetWeight.projection X) ⟶
                  Over.mk (smallLeftUnstraighteningProjection (spaceDiagram X)) from
                Over.homMk (SetWeight.elementsComparisonNatural X)
                  (SetWeight.elementsComparisonNatural_projection X))) ≫
            (SSet.uliftFunctor.{u + 1, u}).map (setWeightRelativeSectionsIso X G).hom := rfl

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
