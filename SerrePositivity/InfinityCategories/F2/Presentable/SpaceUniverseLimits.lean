module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallSpaceCompact
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomEnriched
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableLimitCharacterization

/-!
概要：指定された空間の宇宙変更は元の極限錐を保つ。
方針：一点空間からの内部 Hom の全自然同型で宇宙変更を共変表現可能関手と比較する。
規約：元の分類による宇宙変更を使い、別の埋め込みへ置き換えない。
使われ方：小さい空間値前層の表現可能性を元の全 Hom と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：一点空間からの元の共変 Hom は指定された空間の宇宙変更と自然同型。
方針：小さい内部 Hom の分類比較と一点からの Hom の恒等比較を合成する。
規約：全関手の自然同型であり、各空間の個別の同値ではない。
使われ方：宇宙変更による全極限錐の保存。 -/
def spaceUniverse_covariantPointIso :
    FunctorIso (covariantRepresentableInfinity (C := SpaceInfinity.{u})
      (coherentNerveVertex pointKanObject.{u})) Compact.spaceUniverseDiagram.{u} := by
  have e : FunctorIso (kanInternalHomInfinity pointKanObject.{u}) (𝟙 SpaceInfinity.{u}) :=
    kanPointHomInfinityComparisonIso
  have h := kanHom_covariantModelIso pointKanObject.{u} ≪≫
    (e.ulift.{u + 1, u + 2}).postcomp Compact.spaceUniverseDiagram
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using h

/-- 概要：空間の指定宇宙変更は任意の存在する全極限錐を保つ。
方針：元の共変表現可能関手の極限保存を全自然同型で移す。
規約：形状の quasicategory 性や小ささの追加条件を要求しない。
使われ方：小さい空間値の密度錐を大きい Hom 値の密度錐へ移す。 -/
lemma spaceUniverseDiagram_map_isLimit {J : SSet.{u + 1}}
    {D : J ⟶ SpaceInfinity.{u}} (c : JoinCone D) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone Compact.spaceUniverseDiagram (JoinCone.ulift c)) :=
  (covariantRepresentableInfinity_isLimit c hc
    (coherentNerveVertex pointKanObject.{u})).of_functorIso
    (spaceUniverse_covariantPointIso.precomp (JoinCone.ulift c).val)

end SerrePositivity.InfinityCategories.F2.Presentable
