module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FibrationInfinity
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldIso

/-!
概要：cocartesian strict transport として現れる図式の元の変換空間による豊穣化。
方針：図式に表現する fibration の存在だけを添え、strict な変換の単位と合成を使う。
規約：任意の strict 図式の変換空間の充填性を仮定せず、標的の表現から証明する。
使われ方：core を取った中間 ∞ 圏と元の straightening の高次の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の cocartesian fibration の strict transport として現れる図式。 -/
def CocartesianTransportDiagramObject (C : Type u) [Category.{u} C] :=
  {F : C ⥤ SSet.{u} // ∃ p : CocartesianFibrationObject (nerve C),
    SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p.val.hom = F}

/-- strict transport 図式の元の全変換空間を Hom とする豊穣構造。 -/
instance cocartesianTransportDiagramObject_enrichedCategory (C : Type u) [Category.{u} C] :
    EnrichedCategory SSet.{u} (CocartesianTransportDiagramObject C) where
  Hom F G := strictDiagramMappingSpace F.val G.val
  id F := strictDiagramMappingIdentity F.val
  comp F G H := strictDiagramMappingComposition F.val G.val H.val
  id_comp F G := strictDiagramMappingIdentity_comp F.val G.val
  comp_id F G := strictDiagramMappingComposition_id F.val G.val
  assoc F G H I := strictDiagramMappingComposition_assoc F.val G.val H.val I.val

/-- 元の変換空間の零単体を通常の射とする圏。 -/
instance cocartesianTransportDiagramObject_category (C : Type u) [Category.{u} C] :
    Category.{u} (CocartesianTransportDiagramObject C) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (CocartesianTransportDiagramObject C)))

/-- 通常の射は豊穣 Hom の単位からの射そのもの。 -/
instance cocartesianTransportDiagramObject_simplicialCategory (C : Type u) [Category.{u} C] :
    SimplicialCategory (CocartesianTransportDiagramObject C) where
  homEquiv := Equiv.refl _
  homEquiv_id F := ForgetEnrichment.homTo_id
    (W := SSet.{u}) (C := CocartesianTransportDiagramObject C) F
  homEquiv_comp f g := ForgetEnrichment.homTo_comp
    (W := SSet.{u}) (C := CocartesianTransportDiagramObject C) f g

/-- 標的の strict transport による表示から、元の全変換空間の充填性を回収する。 -/
instance cocartesianTransportDiagramObject_sHom_quasicategory
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramObject C) :
    Quasicategory (SimplicialCategory.sHom F G) := by
  obtain ⟨q, hq⟩ := G.property
  change Quasicategory (strictDiagramMappingSpace F.val G.val)
  rw [← hq]
  exact strictDiagramMappingSpace_cocartesianStrictTransport_quasicategory F.val q.val.hom

/-- 指定した cocartesian fibration の元の strict transport を図式の対象にする。 -/
def cocartesianTransportDiagramImage {C : Type u} [Category.{u} C]
    (p : CocartesianFibrationObject (nerve C)) : CocartesianTransportDiagramObject C :=
  ⟨SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p.val.hom, p, rfl⟩

end SerrePositivity.InfinityCategories
