module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetCoconeAugmentationCriterion
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedAugmentationSquareTransport

/-!
概要：集合値係数の指定全自然同型に沿って、元の空間値余錐の普遍性を移す。
方針：同じ元の増大と既存 coend の係数移送の四角形を使う。
規約：HTT 4.1.3.1 の既存 comma 判定の係数移送の法則。
使われ方：S8 の Hom による評価を、同じ Yoneda 同型で元の点での評価へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]

/-- 同じ全自然同型で係数を移しても、元の全余錐が同じ comma の収縮から普遍になる。 -/
lemma mappedSetCocone_isColimit_of_contractible_comma_and_iso {D : I ⥤ C} (c : Cocone D)
    {F G : C ⥤ Type u} (e : F ≅ G)
    (hc : ∀ q : Discrete (F.obj c.pt), IsWeaklyContractible
      (nerve (CostructuredArrow (elementsCoconeFunctor (F.mapCocone c)) q))) :
    IsColimitCone (strictNativeCocone (setsToKan.mapCocone (G.mapCocone c))) := by
  let H := setsToKan ⋙ kanObjectForget
  let cF := H.mapCocone (F.mapCocone c)
  let cG := H.mapCocone (G.mapCocone c)
  have he : ∀ i, cF.ι.app i ≫ (H.mapIso (e.app c.pt)).hom =
      (CategoryTheory.Functor.isoWhiskerRight (CategoryTheory.Functor.isoWhiskerLeft D e) H).hom.app i ≫ cG.ι.app i := by
    intro i
    change H.map (F.map (c.ι.app i)) ≫ H.map (e.hom.app c.pt) =
      H.map (e.hom.app (D.obj i)) ≫ H.map (G.map (c.ι.app i))
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg (fun t => H.map t) (e.hom.naturality (c.ι.app i))
  apply strictNativeCocone_isColimit_of_reflectedAugmentation_weak
  apply weightedAugmentation_weak_of_iso_square
    (bousfieldKanWeight Iᵒᵖ ⋙ SSet.opFunctor) cF cG
    (CategoryTheory.Functor.isoWhiskerRight (CategoryTheory.Functor.isoWhiskerLeft D e) H) (H.mapIso (e.app c.pt)) he
  rw [← reflectedBousfieldKanElementsIso_augmentation (F.mapCocone c)]
  apply (isPrecompositionEquivalence_of_iso
    (reflectedBousfieldKanElementsIso (D ⋙ F))).isWeakHomotopyEquivalence.comp
  exact (nerveMap_isLeftCofinal_of_weaklyContractible_comma _ hc).isWeakHomotopyEquivalence.comp
    ((isPrecompositionEquivalence_of_iso
      (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso
        (F.obj c.pt))).isWeakHomotopyEquivalence)

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
