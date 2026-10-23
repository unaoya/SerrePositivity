module

public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramScaffoldIdentities
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportMappingRetraction

/-!
概要：通常の圏の nerve 上の left fibrations の相対 Hom と strict transport 間の strict な変換空間の同値。
方針：変換空間を replacement 上の相対 Hom に同型で移し、universal scaffold による前合成の同値を使う。
規約：coherent な変換空間との比較は引き続き別の証明課題。
使われ方：Kerodon Corollary 5.6.0.6、straightening の写像空間比較の strict な図式側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：標的が left fibration の strict transport である strict な変換空間は Kan 複体。
方針：scaffold 比較の厳密な同型で相対 Hom に移し、そのホーン充填を戻す。
規約：始域の係数図式 F には Kan 性を要求しない。
使われ方：Kerodon Corollary 5.6.0.6、strict な変換空間での関手同型と同値の利用。 -/
instance strictDiagramMappingSpace_leftStrictTransport_kanComplex
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {E : SSet.{u}}
    (q : E ⟶ nerve C) [LeftFibration q] :
    KanComplex (strictDiagramMappingSpace F (leftStrictTransportDiagram q)) := by
  let e := strictDiagramMappingScaffoldIso F q
  apply kanComplex_of_rightHornFillers
  intro n i _ σ
  obtain ⟨H, hH⟩ := KanComplex.hornFilling (σ ≫ e.hom)
  refine ⟨H ≫ e.inv, ?_⟩
  rw [← Category.assoc, ← hH, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- 概要：strict な変換の scaffold 評価は left fibration を標的とすると同値。
方針：厳密な同型を Kan 複体間の同値として使う。
規約：順方向は既存の scaffold 評価射そのもの。
使われ方：Kerodon Corollary 5.6.0.6、strict transport の写像空間上の同値性の二対三則。 -/
lemma strictDiagramMappingScaffoldMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {E : SSet.{u}}
    (q : E ⟶ nerve C) [LeftFibration q] :
    IsQCatEquivalence (strictDiagramMappingScaffoldMap F q) :=
  (qCatEquivalenceOfIso (strictDiagramMappingScaffoldIso F q)).isQCatEquivalence

/-- 概要：left fibrations の相対 Hom から strict transport の strict な変換空間への実際の比較射は同値。
方針：scaffold の評価との合成を、universal scaffold に沿う相対前合成の同値と同定して消去する。
規約：通常の圏 C は任意。strict な自然変換と coherent な自然変換の同一視は含めない。
使われ方：Kerodon Corollary 5.6.0.6、分類の写像空間比較の strict transport による充満忠実性。 -/
lemma leftStrictTransportMappingSpaceMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    IsQCatEquivalence (leftStrictTransportMappingSpaceMap p q) := by
  apply (strictDiagramMappingScaffoldMap_isQCatEquivalence
    (leftStrictTransportDiagram p) q).cancel_right
  rw [leftStrictTransportMappingSpaceMap_scaffold]
  exact (leftStrictTransportScaffoldRestrictionEquivalence p q).isQCatEquivalence

/-- 概要：元の相対写像空間と strict transport 間の strict な変換空間の同値データ。
方針：実際の比較射の同値性から逆射と二つの関手同型を取り出す。
規約：順方向は leftStrictTransportMappingSpaceMap に固定する。
使われ方：Kerodon Corollary 5.6.0.6、coherent な図式側へ進む前の strict な写像空間の比較。 -/
noncomputable def leftStrictTransportMappingEquivalence
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence (relativeFunctorSpace q p)
      (strictDiagramMappingSpace (leftStrictTransportDiagram p) (leftStrictTransportDiagram q)) :=
  (leftStrictTransportMappingSpaceMap_isQCatEquivalence p q).choose

end SerrePositivity.InfinityCategories
