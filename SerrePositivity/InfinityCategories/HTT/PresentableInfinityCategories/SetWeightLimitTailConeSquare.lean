module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsLimitTailShape
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsLimitNaturality

/-!
概要：G8 の元の後段の形状自然性を、固定端点の錐の全族と空間のホモトピー圏へ渡す。
方針：構成済みの全族同型に元の極限錐比較を後合成し、既存の全族判定を使う。
規約：必要な比較同型を仮定に足さない。元の比較射の両経路そのものを扱う。
使われ方：IS-W1 の四角形②、および①と合わせる後段の入力。
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
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u} (φ : X ⟶ Y)
  {E : SSet.{u + 1}} [Quasicategory E] (hE : IsPresentable E) (M : E _⦋0⦌)
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
  (cX : JoinCone (SetWeight.diagram X F)) (hcX : IsLimitCone cX)
  (cY : JoinCone (SetWeight.diagram Y F)) (hcY : IsLimitCone cY)

/-- 元の後段の二経路は、指定極限錐の固定端点模型で全族として同型。 -/
def setWeightLimitTailConeFamilyIso :
    FunctorIso
      (((SSet.uliftFunctor.{u + 1, u}).map
        (setWeightActualSectionsRestriction φ (F ≫ (spaceTensorData hE M).hom)) ≫
          (setWeightSectionsLimitTail X hE M F cX hcX).hom) ≫
        SetWeight.limitConeEndpointComparison cX M)
      (((setWeightSectionsLimitTail Y hE M F cY hcY).hom ≫
        postcompose M (SSet.Truncated.HomotopyCategory.homMk
          (SetWeight.sectionsMap φ F cX hcX cY hcY))) ≫
        SetWeight.limitConeEndpointComparison cX M) :=
  FunctorIso.postcomp (setWeightSectionsLimitTail_shapeIso φ hE M F cX hcX cY hcY)
    (SetWeight.limitConeEndpointComparison cX M)

/-- 元の後段の二経路は、空間のホモトピー圏で同じ射を定める。 -/
lemma setWeightLimitTail_homMk_eq :
    let A := (SSet.uliftFunctor.{u + 1, u}).obj
      (coherentSpaceSectionsObject (SetWeight.diagram Y (F ≫ (spaceTensorData hE M).hom))).obj
    let a := (SSet.uliftFunctor.{u + 1, u}).map
      (setWeightActualSectionsRestriction φ (F ≫ (spaceTensorData hE M).hom)) ≫
        (setWeightSectionsLimitTail X hE M F cX hcX).hom
    let b := (setWeightSectionsLimitTail Y hE M F cY hcY).hom ≫
      postcompose M (SSet.Truncated.HomotopyCategory.homMk
        (SetWeight.sectionsMap φ F cX hcX cY hcY))
    Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (C := KanObject.{u + 1})
        (X := ⟨A, inferInstance⟩) (Y := ⟨Basic.pinchedHom M cX.vertex, inferInstance⟩) a).toTruncated =
    Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (C := KanObject.{u + 1})
        (X := ⟨A, inferInstance⟩) (Y := ⟨Basic.pinchedHom M cX.vertex, inferInstance⟩) b).toTruncated := by
  exact SetWeight.limitConeMap_homMk_eq_of_coneFamilyIso cX hcX M _ _
    (setWeightLimitTailConeFamilyIso φ hE M F cX hcX cY hcY)

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
