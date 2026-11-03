module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FilteredIntervalReplacement

/-!
概要：二段の path 引き戻しは通常の filtered 余極限と同型を介して交換する。
方針：有限極限保存と path 置換の比較同型を終点評価の上で合成する。
規約：値の Kan 性は不要。native な homotopy pullback との比較は別に行う。
使われ方：𝒮 の filtered 余極限と有限極限の交換の具体的な模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] [IsFiltered I] {F G H : I ⥤ SSet.{u}}

/-- 概要：path 引き戻し図式の余極限は余極限の二射の path 引き戻しに同型。
方針：二段目の有限極限比較で path 置換の比較同型を使う。
規約：両端評価を保つ標準比較。使われ方：filtered な homotopy pullback の交換。 -/
def intervalPullbackColimitIso (η : F ⟶ G) (θ : H ⟶ G) :
    colimit (intervalPullbackDiagram η θ) ≅ intervalPullback (colim.map η) (colim.map θ) :=
  filteredPullbackIso (intervalReplacementDiagramEndpoint η) θ ≪≫
    asIso (pullback.map (colim.map (intervalReplacementDiagramEndpoint η)) (colim.map θ)
      (intervalReplacementEndpoint (colim.map η)) (colim.map θ)
      (intervalReplacementColimitIso η).hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, intervalReplacementColimitIso_endpoint])
      (by rw [Category.comp_id, Category.id_comp]))

/-- 概要：path 引き戻しの比較は path 置換の座標を保つ。
方針：二段目の引き戻しの第一射影を計算する。
規約：元の標準比較の式。使われ方：path と第一入力の整合性。 -/
lemma intervalPullbackColimitIso_fst (η : F ⟶ G) (θ : H ⟶ G) :
    (intervalPullbackColimitIso η θ).hom ≫
        pullback.fst (intervalReplacementEndpoint (colim.map η)) (colim.map θ) =
      colim.map (pullback.fst (intervalReplacementDiagramEndpoint η) θ) ≫
        (intervalReplacementColimitIso η).hom := by
  rw [intervalPullbackColimitIso, Iso.trans_hom, Category.assoc, asIso_hom,
    pullback.map, pullback.lift_fst, ← Category.assoc, filteredPullbackIso_fst]

/-- 概要：path 引き戻しの比較は第二入力への射影を保つ。
方針：二段目の引き戻しの第二射影を計算する。
規約：元の通常の colimit の誘導射。使われ方：第二入力の整合性。 -/
lemma intervalPullbackColimitIso_snd (η : F ⟶ G) (θ : H ⟶ G) :
    (intervalPullbackColimitIso η θ).hom ≫
        pullback.snd (intervalReplacementEndpoint (colim.map η)) (colim.map θ) =
      colim.map (pullback.snd (intervalReplacementDiagramEndpoint η) θ) := by
  rw [intervalPullbackColimitIso, Iso.trans_hom, Category.assoc, asIso_hom,
    pullback.map, pullback.lift_snd, Category.comp_id, filteredPullbackIso_snd]

/-- 概要：path 引き戻しの比較は元の第一入力への射影も保つ。
方針：path 置換の第二射影の式を合成する。
規約：置換前の F の colimit への実際の射。使われ方：元の cospan の比較。 -/
lemma intervalPullbackColimitIso_left (η : F ⟶ G) (θ : H ⟶ G) :
    (intervalPullbackColimitIso η θ).hom ≫
        pullback.fst (intervalReplacementEndpoint (colim.map η)) (colim.map θ) ≫
          pullback.snd ((intervalEndpointNatTrans 0).app (colimit G)) (colim.map η) =
      colim.map (pullback.fst (intervalReplacementDiagramEndpoint η) θ ≫
        pullback.snd (diagramIntervalEndpoint G 0) η) := by
  rw [← Category.assoc, intervalPullbackColimitIso_fst, Category.assoc,
    intervalReplacementColimitIso_snd, ← CategoryTheory.Functor.map_comp]

/-- 概要：二段の比較は path 座標全体も区間関手の比較へ送る。
方針：二段目と一段目の第一射影の式を合成する。
規約：両端点だけでなく全ての高次の path を保持する。使われ方：指定円柱との整合。 -/
lemma intervalPullbackColimitIso_path (η : F ⟶ G) (θ : H ⟶ G) :
    (intervalPullbackColimitIso η θ).hom ≫
        pullback.fst (intervalReplacementEndpoint (colim.map η)) (colim.map θ) ≫
          pullback.fst ((intervalEndpointNatTrans 0).app (colimit G)) (colim.map η) =
      colim.map (pullback.fst (intervalReplacementDiagramEndpoint η) θ ≫
        pullback.fst (diagramIntervalEndpoint G 0) η) ≫ (intervalColimitIso G).hom := by
  rw [← Category.assoc, intervalPullbackColimitIso_fst, Category.assoc,
    intervalReplacementColimitIso_fst, ← Category.assoc, ← CategoryTheory.Functor.map_comp]

end SerrePositivity.InfinityCategories.F2
