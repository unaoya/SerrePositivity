module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation

/-!
概要：通常の図式の区間関手と二段の引き戻しによる path 模型。
方針：区間の端点評価を自然変換にし、関手圏で引き戻しを取る。
規約：元の値に Kan 性は要求しない。∞ 極限性は別に証明する。
使われ方：homotopy pullback の filtered 連続性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：区間関手の指定端点の評価は単体集合全体で自然。
方針：各次数で後合成と頂点の評価を交換する。
規約：0 は始点、1 は終点。使われ方：図式全体の path 置換。 -/
def intervalEndpointNatTrans (e : Fin 2) : ihom (Δ[1] : SSet.{u}) ⟶ 𝟭 SSet.{u} where
  app Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm e)
  naturality X Y f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    rfl

variable {I : Type u} [SmallCategory I] {F G H : I ⥤ SSet.{u}}

/-- 概要：図式の区間関手を元の図式へ指定端点で評価する。
方針：端点評価の自然変換を図式で前合成する。
規約：指定された構造射を保持する。使われ方：関手圏の引き戻しの一脚。 -/
def diagramIntervalEndpoint (G : I ⥤ SSet.{u}) (e : Fin 2) :
    G ⋙ ihom (Δ[1] : SSet.{u}) ⟶ G :=
  Functor.whiskerLeft G (intervalEndpointNatTrans e)

/-- 概要：単体集合の射を、その像から始まる path で置き換える。
方針：区間関手の始点評価を元の射に沿って引き戻す。
規約：第一座標は path。使われ方：各段と余極限後の比較の標的。 -/
def intervalReplacement {X Y : SSet.{u}} (f : X ⟶ Y) : SSet.{u} :=
  pullback ((intervalEndpointNatTrans 0).app Y) f

/-- 概要：path 置換の終点の射。
方針：path 座標を終点で評価する。
規約：元の射 f と始点で一致する path を使う。使われ方：二段目の引き戻し。 -/
def intervalReplacementEndpoint {X Y : SSet.{u}} (f : X ⟶ Y) : intervalReplacement f ⟶ Y :=
  pullback.fst ((intervalEndpointNatTrans 0).app Y) f ≫ (intervalEndpointNatTrans 1).app Y

/-- 概要：自然変換の各段を path で置き換えた関手圏の図式。
方針：始点評価と元の自然変換の引き戻しを取る。
規約：添字圏は元の I のまま。使われ方：filtered な path 置換の表示。 -/
def intervalReplacementDiagram (η : F ⟶ G) : I ⥤ SSet.{u} :=
  pullback (diagramIntervalEndpoint G 0) η

/-- 概要：図式全体の path 置換から元の終域図式への終点評価。
方針：path 座標の射影と図式の終点評価を合成する。
規約：自然変換全体として定義する。使われ方：二段目の関手圏の引き戻し。 -/
def intervalReplacementDiagramEndpoint (η : F ⟶ G) : intervalReplacementDiagram η ⟶ G :=
  pullback.fst (diagramIntervalEndpoint G 0) η ≫ diagramIntervalEndpoint G 1

/-- 概要：二射の path による引き戻し模型。
方針：第一射を path 置換し、その終点を第二射で引き戻す。
規約：通常の圏の実際の二段の引き戻し。使われ方：homotopy pullback の模型。 -/
def intervalPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) : SSet.{u} :=
  pullback (intervalReplacementEndpoint f) g

/-- 概要：図式全体の path による引き戻し模型。
方針：関手圏で二段の引き戻しを作る。
規約：各段との同定は評価の標準同型を用いる。使われ方：filtered 連続性の始域。 -/
def intervalPullbackDiagram (η : F ⟶ G) (θ : H ⟶ G) : I ⥤ SSet.{u} :=
  pullback (intervalReplacementDiagramEndpoint η) θ

end SerrePositivity.InfinityCategories.Project.FilteredExchange
