module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback

/-!
概要：fiber ごとの path 引き戻しの比較は二入力と path の全座標を保つ。
方針：二段の引き戻しの射影式を順に合成する。
規約：両端点だけでなく元の path の全単体を保持する。
使われ方：一般 coherent な cospan の比較の指定データの照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：第一段の比較は元の第一入力を保つ。
方針：引き戻しの第二射影。規約：厳密な等式。使われ方：二入力の照合。 -/
lemma fiberwiseIntervalReplacementComparison_left :
    fiberwiseIntervalReplacementComparison p f ≫
      pullback.snd ((intervalEndpointNatTrans 0).app H) f =
        pullback.snd (fiberwiseIntervalEndpoint p 0) f := by
  rw [fiberwiseIntervalReplacementComparison, pullback.map, pullback.lift_snd, Category.comp_id]

/-- 概要：第一段の比較は底を忘れるだけで元の path を保つ。
方針：引き戻しの第一射影。規約：全 path 座標。使われ方：指定 path の追跡。 -/
lemma fiberwiseIntervalReplacementComparison_path :
    fiberwiseIntervalReplacementComparison p f ≫
      pullback.fst ((intervalEndpointNatTrans 0).app H) f =
        pullback.fst (fiberwiseIntervalEndpoint p 0) f ≫
          pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) :=
  pullback.lift_fst _ _ _

/-- 概要：第二段の比較は第一段の座標を第一段の比較へ送る。
方針：引き戻しの第一射影。規約：元の置換座標。使われ方：path と第一入力の照合。 -/
lemma fiberwiseIntervalPullbackComparison_fst :
    fiberwiseIntervalPullbackComparison p f g ≫
      pullback.fst (intervalReplacementEndpoint f) g =
        pullback.fst (fiberwiseIntervalReplacementEndpoint p f) g ≫
          fiberwiseIntervalReplacementComparison p f :=
  pullback.lift_fst _ _ _

/-- 概要：第二段の比較は元の第二入力を保つ。
方針：引き戻しの第二射影。規約：厳密な等式。使われ方：二入力の照合。 -/
lemma fiberwiseIntervalPullbackComparison_right :
    fiberwiseIntervalPullbackComparison p f g ≫
      pullback.snd (intervalReplacementEndpoint f) g =
        pullback.snd (fiberwiseIntervalReplacementEndpoint p f) g := by
  rw [fiberwiseIntervalPullbackComparison, pullback.map, pullback.lift_snd, Category.comp_id]

/-- 概要：全比較は元の第一入力も保つ。
方針：二段の射影式を合成する。規約：元の E。使われ方：cospan の比較の第一脚。 -/
lemma fiberwiseIntervalPullbackComparison_left :
    fiberwiseIntervalPullbackComparison p f g ≫
      pullback.fst (intervalReplacementEndpoint f) g ≫
        pullback.snd ((intervalEndpointNatTrans 0).app H) f =
      pullback.fst (fiberwiseIntervalReplacementEndpoint p f) g ≫
        pullback.snd (fiberwiseIntervalEndpoint p 0) f := by
  rw [← Category.assoc, fiberwiseIntervalPullbackComparison_fst, Category.assoc,
    fiberwiseIntervalReplacementComparison_left]

/-- 概要：全比較は元の path の全単体を保つ。
方針：二段の第一射影を合成する。規約：全 path 座標。使われ方：指定円柱の照合。 -/
lemma fiberwiseIntervalPullbackComparison_path :
    fiberwiseIntervalPullbackComparison p f g ≫
      pullback.fst (intervalReplacementEndpoint f) g ≫
        pullback.fst ((intervalEndpointNatTrans 0).app H) f =
      pullback.fst (fiberwiseIntervalReplacementEndpoint p f) g ≫
        pullback.fst (fiberwiseIntervalEndpoint p 0) f ≫
          pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) := by
  rw [← Category.assoc, fiberwiseIntervalPullbackComparison_fst, Category.assoc,
    fiberwiseIntervalReplacementComparison_path]

end SerrePositivity.InfinityCategories.F2
