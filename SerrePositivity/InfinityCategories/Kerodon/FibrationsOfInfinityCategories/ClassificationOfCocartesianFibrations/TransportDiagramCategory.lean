module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FibrationInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldIso

/-!
概要：cocartesian strict transport として現れる図式の元の変換空間による豊穣化。
方針：図式に表現する fibration の存在だけを添え、strict な変換の単位と合成を使う。
規約：任意の strict 図式の変換空間の充填性を仮定せず、標的の表現から証明する。
使われ方：core を取った中間 ∞ 圏と元の straightening の高次の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の cocartesian fibration の strict transport として現れる図式。 -/
def CocartesianTransportDiagramObject (C : Type u) [Category.{u} C] :=
  {F : C ⥤ SSet.{u} // ∃ p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p.val.hom = F}

/-- strict transport 図式の元の全変換空間を Hom とする豊穣構造。 -/
instance cocartesianTransportDiagramObject_enrichedCategory (C : Type u) [Category.{u} C] :
    EnrichedCategory SSet.{u} (CocartesianTransportDiagramObject C) where
  Hom F G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F.val G.val
  id F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity F.val
  comp F G H := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition F.val G.val H.val
  id_comp F G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity_comp F.val G.val
  comp_id F G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition_id F.val G.val
  assoc F G H I := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition_assoc F.val G.val H.val I.val

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
  change Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F.val G.val)
  rw [← hq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingSpace_cocartesianStrictTransport_quasicategory F.val q.val.hom

/-- 指定した cocartesian fibration の元の strict transport を図式の対象にする。 -/
def cocartesianTransportDiagramImage {C : Type u} [Category.{u} C]
    (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationObject (nerve C)) : CocartesianTransportDiagramObject C :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p.val.hom, p, rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
