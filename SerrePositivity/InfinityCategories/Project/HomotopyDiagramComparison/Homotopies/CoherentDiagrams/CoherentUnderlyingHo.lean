module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：元の通常の射と coherent nerve のホモトピー圏の関手を照合する。
方針：元の Hom 同型の合成式と、元の通常の置換比較の自然性を使用する。
規約：coherent な cf 置換関手の射との照合は別工程。使われ方：HTT 5.2.4.6。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 元の通常の対象・射を、標準頂点・辺の類によって coherent nerve の h へ写す。 -/
def coherentUnderlyingHoFunctor (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    C ⥤ hoFunctor.obj (SimplicialNerve C) where
  obj X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
  map f := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated
  map_id X := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id,
      SSet.Truncated.HomotopyCategory.homMk_id]
    rfl
  map_comp f g := (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).toTruncated).symm

/-- 元の豊穣関手の通常の作用は、同じ豊穣単位からの射の作用と整合する。 -/
lemma enrichedUnderlying_eHom_map
    {A B : Type v} [Category.{u} A] [Category.{u} B]
    [SimplicialCategory A] [SimplicialCategory B]
    (F : EnrichedFunctor SSet.{u} A B) {X Y : A} (f : X ⟶ Y) :
    eHomEquiv SSet ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor F).map f) =
      eHomEquiv SSet f ≫ F.map X Y := by
  apply (SSet.unitHomEquiv _).injective
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex F f

/-- 通常の nerve の coherent 表示は、元の豊穣関手の作用に自然である。 -/
lemma nerveToCoherent_enriched_naturality
    {A B : Type v} [Category.{u} A] [Category.{u} B]
    [SimplicialCategory A] [SimplicialCategory B] (F : EnrichedFunctor SSet.{u} A B) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Φ
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _).comp SSet F
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram_postcomp]
  rfl

/-- 元の通常射から作る coherent 辺は、元の豊穣関手の作用と可換。 -/
lemma coherentNerveMap_coherentEdge
    {A B : Type v} [Category.{u} A] [Category.{u} B]
    [SimplicialCategory A] [SimplicialCategory B] (F : EnrichedFunctor SSet.{u} A B)
    {X Y : A} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor F).map f)).edge := by
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f))
    (nerveToCoherent_enriched_naturality F)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, NatTrans.comp_app, types_comp_apply,
    nerveMap_app_mk₁] using h.symm

/-- 元の通常射の h への関手は、豊穣関手の coherent nerve の作用と自然同型で整合する。 -/
def coherentUnderlyingHoMapIso
    {A B : Type v} [Category.{u} A] [Category.{u} B]
    [SimplicialCategory A] [SimplicialCategory B] (F : EnrichedFunctor SSet.{u} A B) :
    coherentUnderlyingHoFunctor A ⋙ (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F)).toFunctor ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor F ⋙ coherentUnderlyingHoFunctor B :=
  NatIso.ofComponents (fun X ↦ eqToIso
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F X))) (fun {X Y} f ↦ by
    apply (Iso.inv_comp_eq (eqToIso
      (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F X)))).1
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex F Y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor F).map f)).toTruncated
      (coherentNerveMap_coherentEdge F f))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
