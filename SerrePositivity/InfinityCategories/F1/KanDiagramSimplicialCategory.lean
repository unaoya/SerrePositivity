module

public import SerrePositivity.InfinityCategories.F1.StrictTransportDiagramInfinity

/-!
概要：通常の圏上の全ての strict な Kan 値図式の単体的圏。
方針：対象ごとの内部 Hom の族に厳密な自然性を課した変換空間で豊穣化する。
規約：全ての Hom の Kan 性や coherent nerve の quasicategory 性は主張しない。
使われ方：Kerodon Corollary 5.6.0.6、豊穣的に自然な図式の族の共同評価の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：通常の圏 C 上の任意の strict な Kan 値図式を束縛する。
方針：既存の関手圏と独立の通常の Hom を与えるため、図式を自明な部分型に包む。
規約：対象には strict transport の像であるという条件を課さない。
使われ方：Kerodon §5.3.1、strict な図式の族の coherent な共同評価。 -/
def KanDiagramObject (C : Type u) [Category.{u} C] := {F : C ⥤ KanObject.{u} // True}

/-- 概要：全ての strict な Kan 値図式を変換空間で豊穣化する。
方針：strict な変換の単位・合成とその法則を使う。
規約：変換空間の Kan 性はこの構造には含めない。
使われ方：Kerodon §5.3.1、豊穣自然変換の共同評価の単位と合成。 -/
instance kanDiagramObject_enrichedCategory (C : Type u) [Category.{u} C] :
    EnrichedCategory SSet.{u} (KanDiagramObject C) where
  Hom F G := strictDiagramMappingSpace (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)
  id F := strictDiagramMappingIdentity (F.val ⋙ kanObjectForget)
  comp F G H := strictDiagramMappingComposition
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) (H.val ⋙ kanObjectForget)
  id_comp F G := strictDiagramMappingIdentity_comp
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)
  comp_id F G := strictDiagramMappingComposition_id
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)
  assoc F G H I := strictDiagramMappingComposition_assoc
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)
    (H.val ⋙ kanObjectForget) (I.val ⋙ kanObjectForget)

/-- 概要：strict な Kan 値図式の通常の射を豊穣単位からの射として定める。
方針：豊穣圏の underlying category を使う。
規約：通常の射は strict な変換空間の零単体に対応する。
使われ方：Kerodon §2.4.3、図式の coherent nerve の通常の圏構造。 -/
instance kanDiagramObject_category (C : Type u) [Category.{u} C] :
    Category.{u} (KanDiagramObject C) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (KanDiagramObject C)))

/-- 概要：strict な Kan 値図式の豊穣構造と通常の圏構造を整合させる。
方針：underlying category の射を同じ豊穣射へ対応させる。
規約：Hom の局所 Kan 性は仮定しない。
使われ方：Kerodon §2.4.3、strict な図式の coherent nerve を構成する入力。 -/
instance kanDiagramObject_simplicialCategory (C : Type u) [Category.{u} C] :
    SimplicialCategory (KanDiagramObject C) where
  homEquiv := Equiv.refl _
  homEquiv_id F := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := KanDiagramObject C) F
  homEquiv_comp f g := by
    exact ForgetEnrichment.homTo_comp (W := SSet.{u}) (C := KanDiagramObject C) f g

/-- 概要：全ての strict な Kan 値図式の coherent nerve。
方針：構成した単体的圏の coherent nerve を取る。
規約：一般に quasicategory であるという主張は含めない。
使われ方：Kerodon Corollary 5.6.0.6、局所 Kan な始域から図式の族を写す中間の単体集合。 -/
noncomputable def KanDiagramNerve (C : Type u) [Category.{u} C] : SSet.{u + 1} :=
  SimplicialNerve (KanDiagramObject C)

end SerrePositivity.InfinityCategories
