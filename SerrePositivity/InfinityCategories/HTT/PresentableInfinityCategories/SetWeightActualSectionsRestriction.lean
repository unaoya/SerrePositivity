module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SectionsLimitShapeValueComparison
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality

/-!
概要：要素の圏の射に沿う実切断制限を、元の表示のまま指定する。
方針：元の要素写像と図式の等式を一般の正規化した実切断制限へ入れる。
規約：選んだ極限の普遍射から制限を再定義しない。
使われ方：G8 の正本の後段に渡す全族の制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}

/-- 元の要素の圏に沿う、小さい切断空間の実際の制限。 -/
def setWeightActualSectionsRestriction (φ : X ⟶ Y)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    (coherentSpaceSectionsObject (SetWeight.diagram Y F)).obj ⟶
      (coherentSpaceSectionsObject (SetWeight.diagram X F)).obj :=
  normalizedSmallSectionsRestriction (SetWeight.diagram Y F) (SetWeight.diagram X F)
    (nerveMap φ.mapElements) (SetWeight.elementsMap_diagram φ F)

/-- 指定された要素の圏の制限は、元の錐の値からの切断写像と全族で可換。 -/
def setWeightConeValue_restrictionIso (φ : X ⟶ Y)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u})
    (c : JoinCone (SetWeight.diagram Y F)) :
    FunctorIso
      (coneSectionsValueMapAt (SetWeight.diagram Y F) c c.vertex rfl ≫
        (SSet.uliftFunctor.{u + 1, u}).map (setWeightActualSectionsRestriction φ F))
      (coneSectionsValueMapAt (SetWeight.diagram X F)
        (SetWeight.restrictSectionsCone φ F c) c.vertex
        (SetWeight.restrictSectionsCone_vertex φ F c)) := by
  exact coneSectionsValueMapAt_normalizedShapeIso (SetWeight.diagram Y F)
    (SetWeight.diagram X F) (nerveMap φ.mapElements) (SetWeight.elementsMap_diagram φ F)
    c (SetWeight.restrictSectionsCone φ F c) rfl c.vertex rfl
      (SetWeight.restrictSectionsCone_vertex φ F c)

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
