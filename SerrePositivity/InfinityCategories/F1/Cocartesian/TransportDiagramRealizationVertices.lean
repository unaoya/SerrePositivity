module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramRealizationComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StraighteningVertices

/-!
概要：中間の実現は元の strict transport 図式そのものを Cat∞ 値関手へ写す。
方針：各値を QCat の対象に束ね、表示する fibration と厳密な分解等式で頂点を計算する。
規約：図式の代表の存在は等式の証明にだけ用い、実現の定義へ選択を持ち込まない。
使われ方：実現の実際の区間 Hom 作用の端点の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の図式とその全輸送を、同じ QCat 値の通常の関手に束ねる。 -/
def cocartesianTransportDiagramValueFunctor {C : Type u} [Category.{u} C]
    (F : CocartesianTransportDiagramCategory C) : C ⥤ QCat.{u} where
  obj c := cocartesianTransportDiagramValue F c
  map f := F.val.map f
  map_id c := F.val.map_id c
  map_comp f g := F.val.map_comp f g

/-- 中間の実現の頂点での値は、同じ元の図式の coherent nerve 表示。 -/
lemma cocartesianTransportDiagramRealization_vertex
    {C : Type u} [Category.{u} C] (F : CocartesianTransportDiagramCategory C) :
    (cocartesianTransportDiagramRealization C).app (Opposite.op ⦋0⦌) (coherentNerveVertex F) =
      functorVertex (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F)) := by
  obtain ⟨p, hp⟩ := F.property
  have hF : (show CocartesianTransportDiagramCategory C from cocartesianTransportDiagramImage p) =
      F := Subtype.ext hp
  rw [← hF, ← cocartesianStrictTransportInfinityMap_vertex]
  change ((cocartesianStrictTransportInfinityMap C ≫ cocartesianTransportDiagramRealization C).app
    (Opposite.op ⦋0⦌)) (coherentNerveVertex
      (show CocartesianFibrationCategory (nerve C) from p)) = _
  rw [cocartesianStrictTransportInfinityMap_realization]
  exact cocartesianStraighteningCoherentMap_vertex p.val.hom

end SerrePositivity.InfinityCategories
