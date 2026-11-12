module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FilteredIntervalColimit
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FilteredFiniteLimits

/-!
概要：path 置換は通常の filtered 余極限と標準同型を介して交換する。
方針：引き戻しの保存と区間関手の連続性を、始点評価を保つ同型で合成する。
規約：元の図式の値に Kan 性は不要。
使われ方：二段の引き戻しによる homotopy pullback の filtered 連続性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] [IsFiltered I] {F G : I ⥤ SSet.{u}}

/-- 概要：図式全体の path 置換の余極限は余極限の射の path 置換に同型。
方針：有限極限の標準比較の後で区間関手の比較同型を引き戻す。
規約：元の比較射と元の図式の座標を保持する。使われ方：二段目の引き戻し。 -/
def intervalReplacementColimitIso (η : F ⟶ G) :
    colimit (intervalReplacementDiagram η) ≅ intervalReplacement (colim.map η) :=
  filteredPullbackIso (diagramIntervalEndpoint G 0) η ≪≫
    asIso (pullback.map (colim.map (diagramIntervalEndpoint G 0)) (colim.map η)
      ((intervalEndpointNatTrans 0).app (colimit G)) (colim.map η)
      (intervalColimitIso G).hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, intervalColimitIso_endpoint])
      (by rw [Category.comp_id, Category.id_comp]))

/-- 概要：path 置換の比較同型は path 座標の余極限を区間関手の比較へ送る。
方針：二段の引き戻し比較の第一射影の式を使う。
規約：高次の path もそのまま比較する。使われ方：終点評価との整合。 -/
lemma intervalReplacementColimitIso_fst (η : F ⟶ G) :
    (intervalReplacementColimitIso η).hom ≫
        pullback.fst ((intervalEndpointNatTrans 0).app (colimit G)) (colim.map η) =
      colim.map (pullback.fst (diagramIntervalEndpoint G 0) η) ≫ (intervalColimitIso G).hom := by
  rw [intervalReplacementColimitIso, Iso.trans_hom, Category.assoc, asIso_hom,
    pullback.map, pullback.lift_fst, ← Category.assoc, filteredPullbackIso_fst]

/-- 概要：path 置換の比較同型は元の始域図式の座標を保つ。
方針：二段の引き戻し比較の第二射影の式を使う。
規約：実際の colimit の誘導射。使われ方：元の入力との比較。 -/
lemma intervalReplacementColimitIso_snd (η : F ⟶ G) :
    (intervalReplacementColimitIso η).hom ≫
        pullback.snd ((intervalEndpointNatTrans 0).app (colimit G)) (colim.map η) =
      colim.map (pullback.snd (diagramIntervalEndpoint G 0) η) := by
  rw [intervalReplacementColimitIso, Iso.trans_hom, Category.assoc, asIso_hom,
    pullback.map, pullback.lift_snd, Category.comp_id, filteredPullbackIso_snd]

/-- 概要：path 置換の比較同型は図式の終点評価の余極限と可換。
方針：path 座標の式と区間関手の両端の評価の連続性を合成する。
規約：元の図式の自然変換全体の等式。使われ方：二段目の比較の可換条件。 -/
lemma intervalReplacementColimitIso_endpoint (η : F ⟶ G) :
    (intervalReplacementColimitIso η).hom ≫ intervalReplacementEndpoint (colim.map η) =
      colim.map (intervalReplacementDiagramEndpoint η) := by
  change (intervalReplacementColimitIso η).hom ≫
    (pullback.fst ((intervalEndpointNatTrans 0).app (colimit G)) (colim.map η) ≫
      (intervalEndpointNatTrans 1).app (colimit G)) = _
  rw [← Category.assoc, intervalReplacementColimitIso_fst,
    Category.assoc, intervalColimitIso_endpoint, ← CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.F2
