module

public import SerrePositivity.KST.Spectra.SpectrumMorphisms
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlyingCoherence
public import SerrePositivity.CategoryTheory.Enriched.BaseChange
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-!
概要：点つき単体集合の単体的豊穣構造。
方針：閉 smash の自己豊穣を、基点を忘れる lax monoidal 関手で移す。
規約：合成・単位・通常の射との比較は既存の通常の圏論から証明する。
使われ方：HTT A.3.3、BF 1978 §2。スペクトルの各段の写像空間の合成。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedEnrichment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき内部 Hom を写像単体集合とする単体的圏。
方針：閉 smash の自己豊穣の基点を忘れて通常の圏構造へ接続する。
規約：この定義は局所 Kan 性を仮定しない。
使われ方：HTT A.3.3、BF 1978 §2。段ごとの写像空間。 -/
@[instance_reducible]
def simplicialCategory : SimplicialCategory PointedSimplicialSet.{u} := by
  let : EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}
  exact TransportOrdinaryEnrichment.ordinaryCategory PointedSimplicialSet.forget.{u}
    PointedSimplicialSet.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
    PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}

local instance : SimplicialCategory PointedSimplicialSet.{u} := simplicialCategory

/-- 概要：移送した豊穣 Hom は等化子で構成した点つき Hom の基礎単体集合。
方針：移送の対象の定義を読む。
規約：X と Y に Kan 性は不要。
使われ方：BF 1978 §2。写像空間の構成の一致。 -/
theorem hom_eq (X Y : PointedSimplicialSet.{u}) :
    SimplicialCategory.sHom X Y = (PointedObject.basedHom X Y).right := rfl

/-- 概要：移送した豊穣の頂点の同値は既に構成した同値と一致する。
方針：curry' と自由基点の Hom 同値の合成を比較する。
規約：実際の通常の射の同値。
使われ方：HTT A.3.3。スペクトルの頂点比較との接続。 -/
theorem vertexEquiv_eq (X Y : PointedSimplicialSet.{u}) :
    SimplicialCategory.homEquiv' X Y = pointedHomVertexEquiv X Y := rfl

/-- 概要：単体的豊穣の源の作用は等化子による制限。
方針：豊穣の移送の自然性と点つき閉構造の pre の一致を用いる。
規約：任意の点つき射 i。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの合成の境界整合性。 -/
theorem whiskerRight_eq {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) : eHomWhiskerRight SSet i Z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z := by
  have h := TransportOrdinaryEnrichment.whiskerRight_map PointedSimplicialSet.forget.{u}
    PointedSimplicialSet.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
    PointedSimplicialSet.forgetUnitHomEquiv_formula.{u} i Z
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at h
  exact h.trans (congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre i Z)).symm

/-- 概要：単体的豊穣の標的の作用は点つき内部 Hom の後合成。
方針：移送した豊穣の自然性と閉構造の後合成の式を使う。
規約：任意の点つき射 f。
使われ方：BF 1978 §2。スペクトルの合成の境界整合性。 -/
theorem whiskerLeft_eq (X : PointedSimplicialSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    (f : Y ⟶ Z) : eHomWhiskerLeft SSet X f = (PointedObject.basedHomMap X f).right := by
  have h := TransportOrdinaryEnrichment.whiskerLeft_map PointedSimplicialSet.forget.{u}
    PointedSimplicialSet.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
    PointedSimplicialSet.forgetUnitHomEquiv_formula.{u} X f
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft] at h
  exact h

end

end SerrePositivity.KST.Spectra.PointedEnrichment
