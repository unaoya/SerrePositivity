module

public import SerrePositivity.InfinityCategories.F1.Coherent.OrderPostcomposition
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges
public import SerrePositivity.InfinityCategories.F1.Coherent.NervePostcomposition
public import SerrePositivity.InfinityCategories.F1B.HomotopyRepresentative

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
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 元の通常の対象・射を、標準頂点・辺の類によって coherent nerve の h へ写す。 -/
def coherentUnderlyingHoFunctor (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    C ⥤ hoFunctor.obj (SimplicialNerve C) where
  obj X := HomotopyCategory.mk (coherentNerveVertex X)
  map f := SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated
  map_id X := by
    rw [coherentNerveEdge_id, SSet.Edge.toTruncated_id,
      SSet.Truncated.HomotopyCategory.homMk_id]
    rfl
  map_comp f g := (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct f g).toTruncated).symm

/-- 元の豊穣関手の通常の作用は、同じ豊穣単位からの射の作用と整合する。 -/
lemma enrichedUnderlying_eHom_map
    {A B : Type v} [Category.{u} A] [Category.{u} B]
    [SimplicialCategory A] [SimplicialCategory B]
    (F : EnrichedFunctor SSet.{u} A B) {X Y : A} (f : X ⟶ Y) :
    eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor F).map f) =
      eHomEquiv SSet f ≫ F.map X Y := by
  apply (SSet.unitHomEquiv _).injective
  exact coherentEnrichedUnderlyingFunctor_vertex F f

/-- 通常の nerve の coherent 表示は、元の豊穣関手の作用に自然である。 -/
lemma nerveToCoherent_enriched_naturality
    {A B : Type v} [Category.{u} A] [Category.{u} B]
    [SimplicialCategory A] [SimplicialCategory B] (F : EnrichedFunctor SSet.{u} A B) :
    nerveMap (coherentEnrichedUnderlyingFunctor F) ≫ nerveToCoherent B =
      nerveToCoherent A ≫ coherentNerveMap F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Φ
  change enrichedFunctorOfOrderDiagram _ = (enrichedFunctorOfOrderDiagram _).comp SSet F
  rw [enrichedFunctorOfOrderDiagram_postcomp]
  rfl

/-- 元の通常射から作る coherent 辺は、元の豊穣関手の作用と可換。 -/
lemma coherentNerveMap_coherentEdge
    {A B : Type v} [Category.{u} A] [Category.{u} B]
    [SimplicialCategory A] [SimplicialCategory B] (F : EnrichedFunctor SSet.{u} A B)
    {X Y : A} (f : X ⟶ Y) :
    (coherentNerveMap F).app (Opposite.op ⦋1⦌) (coherentNerveEdge f).edge =
      (coherentNerveEdge ((coherentEnrichedUnderlyingFunctor F).map f)).edge := by
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f))
    (nerveToCoherent_enriched_naturality F)
  simpa only [coherentNerveEdge_edge, NatTrans.comp_app, types_comp_apply,
    nerveMap_app_mk₁] using h.symm

/-- 元の通常射の h への関手は、豊穣関手の coherent nerve の作用と自然同型で整合する。 -/
def coherentUnderlyingHoMapIso
    {A B : Type v} [Category.{u} A] [Category.{u} B]
    [SimplicialCategory A] [SimplicialCategory B] (F : EnrichedFunctor SSet.{u} A B) :
    coherentUnderlyingHoFunctor A ⋙ (hoFunctor.map (coherentNerveMap F)).toFunctor ≅
      coherentEnrichedUnderlyingFunctor F ⋙ coherentUnderlyingHoFunctor B :=
  NatIso.ofComponents (fun X ↦ eqToIso
    (congrArg HomotopyCategory.mk (coherentNerveMap_vertex F X))) (fun {X Y} f ↦ by
    apply (Iso.inv_comp_eq (eqToIso
      (congrArg HomotopyCategory.mk (coherentNerveMap_vertex F X)))).1
    exact homMk_transport (coherentNerveMap_vertex F X) (coherentNerveMap_vertex F Y)
      ((coherentNerveEdge f).toTruncated.map ((truncation 2).map (coherentNerveMap F)))
      (coherentNerveEdge ((coherentEnrichedUnderlyingFunctor F).map f)).toTruncated
      (coherentNerveMap_coherentEdge F f))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
