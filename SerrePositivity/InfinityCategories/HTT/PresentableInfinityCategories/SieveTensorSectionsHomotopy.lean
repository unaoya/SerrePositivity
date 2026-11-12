module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SieveTensorSectionsNaturality
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsSieveHomotopy

/-!
概要：G8 の篩包含の四角形を、空間のホモトピー圏での等式として取り出す。
方針：元の全族比較を、Kan 複体の coherent nerve 内の射の等式へ送る。
規約：元の篩テンソル辺・切断辺・指定極限・比較の順射をそのまま用いる。
使われ方：BS の篩生成辺に対する局所性の比較。
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
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 正本の G8 比較の篩包含の四角形は、全写像空間のホモトピー圏で可換。 -/
lemma sieveTensorSections_homMk_eq {C : Type u} [SmallCategory C] {U : C} (S : Sieve U)
    {E : SSet.{u + 1}} [Quasicategory E] (hE : IsPresentable E) (M : E _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Cᵒᵖ) ⟶ E)
    (cS : JoinCone (SetWeight.diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (SetWeight.diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    let K : KanObject.{u + 1} :=
      ⟨Basic.pinchedHom (functorVertex (spaceDiagram (yoneda.obj U) ≫ tensorSpaceFunctor hE M))
        (functorVertex F), inferInstance⟩
    let L : KanObject.{u + 1} := ⟨Basic.pinchedHom M cS.vertex, inferInstance⟩
    Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (C := KanObject.{u + 1}) (X := K) (Y := L)
        (show K.obj ⟶ L.obj from precompose (functorVertex F)
          (Truncated.HomotopyCategory.homMk (SetWeight.sieveTensorEdge S hE M).toTruncated) ≫
            (SetWeight.tensorSpaceFunctor_setWeightHomNatural S.functor hE M F cS hcS).hom)).toTruncated =
    Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (C := KanObject.{u + 1}) (X := K) (Y := L)
        (show K.obj ⟶ L.obj from
          (SetWeight.tensorSpaceFunctor_setWeightHomNatural (yoneda.obj U) hE M F cU hcU).hom ≫
          postcompose M (Truncated.HomotopyCategory.homMk
            (SetWeight.sieveSectionsMap S F cS hcS cU hcU).toTruncated))).toTruncated := by
  exact coherentKanEdge_homMk_eq_of_functorIso
    (sieveTensorSections_shapeIso S hE M F cS hcS cU hcU)

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
