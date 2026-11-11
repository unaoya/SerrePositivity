module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram

/-!
概要：関手圏の path 置換と二段の引き戻しを各成分で標準の模型に同定する。
方針：評価の引き戻し保存同型を二度使い、終点評価と元の座標を保持する。
規約：図式の値に Kan 性は不要。
使われ方：filtered な path 模型の各値を Kan 対象として束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F G H : I ⥤ SSet.{u}}

/-- 概要：図式の path 置換の各値は成分の path 置換に同型。
方針：評価の引き戻し保存を使う。
規約：標準の評価比較。使われ方：二段目の評価の比較。 -/
def intervalReplacementObjIso (η : F ⟶ G) (i : I) :
    (intervalReplacementDiagram η).obj i ≅ intervalReplacement (η.app i) :=
  pullbackObjIso (diagramIntervalEndpoint G 0) η i

/-- 概要：各値の比較同型は元の始域への射影を保つ。
方針：評価の引き戻し比較の第二射影の式。
規約：指定した成分の座標。使われ方：元の入力の比較。 -/
lemma intervalReplacementObjIso_snd (η : F ⟶ G) (i : I) :
    (intervalReplacementObjIso η i).hom ≫
        pullback.snd ((intervalEndpointNatTrans 0).app (G.obj i)) (η.app i) =
      (pullback.snd (diagramIntervalEndpoint G 0) η).app i :=
  pullbackObjIso_hom_comp_snd (diagramIntervalEndpoint G 0) η i

/-- 概要：各値の比較同型は終点評価を保つ。
方針：第一射影の式と終点評価の成分を合成する。
規約：射の厳密な等式。使われ方：二段目の比較の可換条件。 -/
lemma intervalReplacementObjIso_endpoint (η : F ⟶ G) (i : I) :
    (intervalReplacementObjIso η i).hom ≫ intervalReplacementEndpoint (η.app i) =
      (intervalReplacementDiagramEndpoint η).app i := by
  change (pullbackObjIso (diagramIntervalEndpoint G 0) η i).hom ≫
    (pullback.fst ((diagramIntervalEndpoint G 0).app i) (η.app i) ≫
      (diagramIntervalEndpoint G 1).app i) =
    (pullback.fst (diagramIntervalEndpoint G 0) η).app i ≫ (diagramIntervalEndpoint G 1).app i
  rw [← Category.assoc, pullbackObjIso_hom_comp_fst]

/-- 概要：二段の path 引き戻し図式の各値は成分の path 引き戻しに同型。
方針：二段目の評価比較の後で path 置換の同型を引き戻す。
規約：元の二成分を同時に保持する。使われ方：各段の native な極限模型。 -/
def intervalPullbackObjIso (η : F ⟶ G) (θ : H ⟶ G) (i : I) :
    (intervalPullbackDiagram η θ).obj i ≅ intervalPullback (η.app i) (θ.app i) :=
  pullbackObjIso (intervalReplacementDiagramEndpoint η) θ i ≪≫
    asIso (pullback.map ((intervalReplacementDiagramEndpoint η).app i) (θ.app i)
      (intervalReplacementEndpoint (η.app i)) (θ.app i)
      (intervalReplacementObjIso η i).hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, intervalReplacementObjIso_endpoint])
      (by rw [Category.comp_id, Category.id_comp]))

/-- 概要：二段の評価の比較は path 置換の座標を保つ。
方針：二段目の評価の第一射影の式を使う。
規約：成分の path 置換の標準同型。使われ方：元の第一入力と path 座標の比較。 -/
lemma intervalPullbackObjIso_fst (η : F ⟶ G) (θ : H ⟶ G) (i : I) :
    (intervalPullbackObjIso η θ i).hom ≫
        pullback.fst (intervalReplacementEndpoint (η.app i)) (θ.app i) =
      (pullback.fst (intervalReplacementDiagramEndpoint η) θ).app i ≫
        (intervalReplacementObjIso η i).hom := by
  rw [intervalPullbackObjIso, Iso.trans_hom, Category.assoc, asIso_hom, pullback.map,
    pullback.lift_fst, ← Category.assoc, pullbackObjIso_hom_comp_fst]

/-- 概要：二段の比較は第二入力への射影を保つ。
方針：二段目の評価の第二射影を計算する。
規約：実際の成分の射。使われ方：native な比較の脚。 -/
lemma intervalPullbackObjIso_snd (η : F ⟶ G) (θ : H ⟶ G) (i : I) :
    (intervalPullbackObjIso η θ i).hom ≫
        pullback.snd (intervalReplacementEndpoint (η.app i)) (θ.app i) =
      (pullback.snd (intervalReplacementDiagramEndpoint η) θ).app i := by
  rw [intervalPullbackObjIso, Iso.trans_hom, Category.assoc, asIso_hom, pullback.map,
    pullback.lift_snd, Category.comp_id, pullbackObjIso_hom_comp_snd]

end SerrePositivity.InfinityCategories.F2
