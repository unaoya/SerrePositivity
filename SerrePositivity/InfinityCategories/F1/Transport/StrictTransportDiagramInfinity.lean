module

public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramComposition
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.Coherent.Quasicategory

/-!
概要：strict transport の像の単体的圏とその coherent nerve。
方針：Kan 値図式のうち strict transport として現れるものを取り、strict な変換空間で豊穣化する。
規約：全ての coherent な図式がこの像に入るという主張はここでは行わない。
使われ方：Kerodon Corollary 5.6.0.6、相対 Hom の同値を coherent nerve の比較へ移す中間の ∞ 圏。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：通常の圏 C 上の strict transport の像に属する Kan 値図式。
方針：Kan 値図式に、それを strict transport として表す left fibration の存在を添える。
規約：存在の証明から代表の選択を対象データへ追加しない。
使われ方：Kerodon §5.3.1、Corollary 5.6.0.6、strict な表現の局所 Kan な単体的圏の対象。 -/
def StrictTransportDiagramObject (C : Type u) [Category.{u} C] :=
  {F : C ⥤ KanObject.{u} // ∃ p : LeftFibrationObject (nerve C),
    leftStrictTransportFunctor p.val.hom = F}

/-- 概要：strict transport の像を strict な自然変換の空間で豊穣化する。
方針：対象ごとの変換の単位・合成とその三法則を適用する。
規約：係数値の Kan 性とは別に、標的が strict transport であることを後で Hom の Kan 性に用いる。
使われ方：Kerodon Corollary 5.6.0.6、strict な表現から coherent nerve を構成する入力。 -/
instance strictTransportDiagramObject_enrichedCategory (C : Type u) [Category.{u} C] :
    EnrichedCategory SSet.{u} (StrictTransportDiagramObject C) where
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

/-- 概要：strict transport の像は豊穣単位から Hom への射を通常の射とする圏をなす。
方針：豊穣圏の underlying category を用いる。
規約：通常の射は strict な変換空間の零単体と同じデータを持つ。
使われ方：Kerodon §2.4.3、strict な表現の coherent nerve の通常の圏構造。 -/
instance strictTransportDiagramObject_category (C : Type u) [Category.{u} C] :
    Category.{u} (StrictTransportDiagramObject C) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (StrictTransportDiagramObject C)))

/-- 概要：strict transport の像の豊穣構造は通常の圏構造と整合し、単体的圏をなす。
方針：underlying category の射を単位からの豊穣射へ恒等の全単射で対応させる。
規約：恒等・合成の整合性は underlying category の法則を使う。
使われ方：Kerodon §2.4.3、coherent nerve の入力の整合性。 -/
instance strictTransportDiagramObject_simplicialCategory (C : Type u) [Category.{u} C] :
    SimplicialCategory (StrictTransportDiagramObject C) where
  homEquiv := Equiv.refl _
  homEquiv_id F := ForgetEnrichment.homTo_id
    (W := SSet.{u}) (C := StrictTransportDiagramObject C) F
  homEquiv_comp f g := by
    exact ForgetEnrichment.homTo_comp
      (W := SSet.{u}) (C := StrictTransportDiagramObject C) f g

/-- 概要：strict transport の像の全ての豊穣 Hom は Kan 複体。
方針：標的図式を strict transport で表し、相対 Hom との同型による Kan 性を適用する。
規約：図式の代表の存在だけを使い、選択した代表は保持しない。
使われ方：Kerodon Corollary 5.6.0.6、coherent nerve の quasicategory 性と Hom 比較の前提。 -/
instance strictTransportDiagramObject_sHom_kanComplex
    {C : Type u} [Category.{u} C] (F G : StrictTransportDiagramObject C) :
    KanComplex (SimplicialCategory.sHom F G) := by
  obtain ⟨q, hq⟩ := G.property
  change KanComplex (strictDiagramMappingSpace (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget))
  rw [← hq]
  change KanComplex (strictDiagramMappingSpace (F.val ⋙ kanObjectForget)
    (leftStrictTransportDiagram q.val.hom))
  infer_instance

/-- 概要：strict transport の像の ∞ 圏。
方針：strict な自然変換空間を Hom とする単体的圏の coherent nerve を取る。
規約：対象の図式の値は u、coherent nerve は u+1。
使われ方：Kerodon Corollary 5.6.0.6、left fibrations と coherent な空間値図式の比較の中間項。 -/
noncomputable def StrictTransportDiagramInfinity (C : Type u) [Category.{u} C] : SSet.{u + 1} :=
  SimplicialNerve (StrictTransportDiagramObject C)

/-- 概要：strict transport の像の coherent nerve は quasicategory。
方針：局所 Kan 性を既存の coherent nerve の定理 γ1 へ適用する。
規約：一般の図式の分類はこの充填性の主張に含まない。
使われ方：Kerodon §2.4.3、Corollary 5.6.0.6、strict な表現の ∞ 圏の比較。 -/
instance strictTransportDiagramInfinity_quasicategory (C : Type u) [Category.{u} C] :
    Quasicategory (StrictTransportDiagramInfinity C) :=
  Coherent.simplicialNerve_quasicategory (StrictTransportDiagramObject C)

/-- 概要：束縛した left fibration の strict transport を像の単体的圏の対象にする。
方針：strict transport 関手に元の fibration を存在の証人として添える。
規約：Kan 複体の値を反転しない。
使われ方：Kerodon Construction 5.3.1.5、Corollary 5.6.0.6、比較関手の対象への作用。 -/
def leftStrictTransportImageObject {C : Type u} [Category.{u} C]
    (p : LeftFibrationObject (nerve C)) : StrictTransportDiagramObject C :=
  ⟨leftStrictTransportFunctor p.val.hom, ⟨p, rfl⟩⟩

end SerrePositivity.InfinityCategories
