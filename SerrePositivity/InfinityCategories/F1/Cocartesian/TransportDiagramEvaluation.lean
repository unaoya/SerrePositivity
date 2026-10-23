module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramMixedHom

/-!
概要：strict transport 図式の core 上の作用を底の一対象で評価する。
方針：元の strict な変換の成分に core 関手を適用し、同じ単位と合成を保つ。
規約：図式と全高次の変換の両方を評価する。
使われ方：実現の区間 Hom 作用を対象成分で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 元の strict な変換の core の全高次を一つの底対象で評価する豊穣関手。 -/
def cocartesianTransportDiagramEvaluationEnriched {C : Type u} [Category.{u} C] (c : C) :
    EnrichedFunctor SSet.{u} (CocartesianTransportDiagramCategory C) QCat.{u} where
  obj F := cocartesianTransportDiagramValue F c
  map F G := quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val c)
  map_id F := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact congrArg (fun k ↦ k.app n s) (strictDiagramMappingIdentity_component F.val c)
  map_comp F G H := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Subtype.ext
    exact congrArg (fun k ↦ k.app n (f.val, g.val))
      (strictDiagramMappingComposition_component F.val G.val H.val c)

/-- 底の恒等射に沿う core の混合作用は、元の対象成分への core 写像と一致する。 -/
lemma cocartesianTransportDiagramMixedHom_base_id {C : Type u} [Category.{u} C]
    (F G : CocartesianTransportDiagramCategory C) (c : C) :
    cocartesianTransportDiagramMixedHom (𝟙 c) F G =
      (cocartesianTransportDiagramEvaluationEnriched c).map F G := by
  change quasicategoryCoreMap (strictDiagramMixedHom (𝟙 c) F.val G.val) = _
  rw [strictDiagramMixedHom, G.val.map_id, (ihom (F.val.obj c)).map_id, Category.comp_id]
  rfl

/-- 対象ごとの元の豊穣評価を coherent nerve の評価へ実現する。 -/
def cocartesianTransportDiagramInfinityEvaluation {C : Type u} [Category.{u} C] (c : C) :
    CocartesianTransportDiagramInfinity C ⟶ CatInfinity.{u} :=
  coherentNerveMap (cocartesianTransportDiagramEvaluationEnriched c)

end SerrePositivity.InfinityCategories
