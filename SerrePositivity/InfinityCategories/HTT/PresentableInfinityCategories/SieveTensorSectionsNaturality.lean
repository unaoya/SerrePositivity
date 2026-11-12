module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsEdgeNaturality
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsLimitTailShape

/-!
概要：篩包含のテンソルと指定極限の切断制限を、元の G8 比較の全族で結ぶ。
方針：元の随伴比較、切断比較①、指定極限への値比較②の三つの自然性を合成する。
規約：任意の前層・指定極限錐・元の辺を保持し、層条件を仮定しない。
使われ方：BS の篩包含で定める局所対象と、構造の切断条件との対応。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 篩包含の元のテンソルの前合成は、正本の G8 比較の下で元の切断辺の後合成に全自然。 -/
def sieveTensorSections_shapeIso {C : Type u} [SmallCategory C] {U : C} (S : Sieve U)
    {E : SSet.{u + 1}} [Quasicategory E] (hE : IsPresentable E) (M : E _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Cᵒᵖ) ⟶ E)
    (cS : JoinCone (SetWeight.diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (SetWeight.diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    FunctorIso
      (precompose (functorVertex F)
        (SSet.Truncated.HomotopyCategory.homMk (SetWeight.sieveTensorEdge S hE M).toTruncated) ≫
          (SetWeight.tensorSpaceFunctor_setWeightHomNatural S.functor hE M F cS hcS).hom)
      ((SetWeight.tensorSpaceFunctor_setWeightHomNatural (yoneda.obj U) hE M F cU hcU).hom ≫
        postcompose M (SSet.Truncated.HomotopyCategory.homMk
          (SetWeight.sieveSectionsMap S F cS hcS cU hcU).toTruncated)) := by
  let G := F ≫ (spaceTensorData hE M).hom
  have h₀ := (SetWeight.tensorSpaceFunctor_diagramHom_weight_naturality
    hE M S.functorInclusion F).postcomp
    ((SetWeight.sectionsEquivalenceNatural S.functor G).hom ≫
      (setWeightSectionsLimitTail S.functor hE M F cS hcS).hom)
  have h₁ := ((setWeightSectionsEquivalenceNatural_shapeIso S.functorInclusion G).postcomp
    (setWeightSectionsLimitTail S.functor hE M F cS hcS).hom).precomp
    (tensorSpaceFunctor_diagramHom hE M (spaceDiagram (yoneda.obj U)) F).hom
  have h₂ := (setWeightSectionsLimitTail_shapeIso S.functorInclusion hE M F cS hcS cU hcU).precomp
    ((tensorSpaceFunctor_diagramHom hE M (spaceDiagram (yoneda.obj U)) F).hom ≫
      (SetWeight.sectionsEquivalenceNatural (yoneda.obj U) G).hom)
  simp only [Category.assoc] at h₀ h₁ h₂
  simpa only [tensorSpaceFunctor_setWeightHomNatural_hom_factor,
    SetWeight.sieveTensorEdge, SetWeight.sieveSectionsMap, G, SSet.Edge.toTruncated,
    FunctorIso, Category.assoc] using
    (h₀ ≪≫ h₁) ≪≫ h₂

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
