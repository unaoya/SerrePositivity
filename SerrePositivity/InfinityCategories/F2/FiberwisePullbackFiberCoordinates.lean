module

public import SerrePositivity.InfinityCategories.F2.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.F2.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F2.FiberwisePathFiberEvaluation
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：path 引き戻しの fiber の三座標を、元の三つの fiber に戻す。
方針：底上の三座標の誘導射と path の fiber 同型を合成する。
規約：同じ元の底の頂点を固定する。
使われ方：fiber の path 引き戻しへの厳密な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)

/-- 概要：fiber の全 path を元の標的 fiber 内の全 path に戻す。
方針：path 座標の fiber 射と内部 Hom の fiber 同型。
規約：元の底の頂点 b。使われ方：fiber 比較の path 座標。 -/
def fiberwisePullbackFiberPath : vertexFiber (fiberwiseIntervalPullbackProjection p f g) b ⟶
    (ihom (Δ[1] : SSet.{u})).obj (vertexFiber p b) :=
  vertexFiberMap (fiberwiseIntervalPullbackProjection p f g) (fiberwiseFunctorProjection p Δ[1])
    (fiberwiseIntervalPullbackPath p f g) (Category.assoc _ _ _) b ≫
      (fiberwiseFunctorFiberIso p Δ[1] b).hom

/-- 概要：fiber の第一座標を元の第一入力の fiber に戻す。
方針：底上の第一射影の誘導射。
規約：元の f ≫ p の fiber。使われ方：fiber 比較の第一脚。 -/
def fiberwisePullbackFiberLeft : vertexFiber (fiberwiseIntervalPullbackProjection p f g) b ⟶
    vertexFiber (f ≫ p) b :=
  vertexFiberMap (fiberwiseIntervalPullbackProjection p f g) (f ≫ p)
    (fiberwiseIntervalPullbackLeft p f g) (by
      simpa only [fiberwiseIntervalPullbackLeft, Category.assoc] using
        fiberwiseIntervalPullback_left_projection p f g) b

/-- 概要：fiber の第二座標を元の第二入力の fiber に戻す。
方針：底上の第二射影の誘導射。
規約：元の g ≫ p の fiber。使われ方：fiber 比較の第二脚。 -/
def fiberwisePullbackFiberRight : vertexFiber (fiberwiseIntervalPullbackProjection p f g) b ⟶
    vertexFiber (g ≫ p) b :=
  vertexFiberMap (fiberwiseIntervalPullbackProjection p f g) (g ≫ p)
    (fiberwiseIntervalPullbackRight p f g) (by
      simpa only [fiberwiseIntervalPullbackRight, Category.assoc] using
        fiberwiseIntervalPullback_right_projection p f g) b

/-- 概要：fiber の path を元の全関手空間へ含めると元の path 座標になる。
方針：path の fiber 同型の包含式と fiber 射の包含式を合成する。
規約：全 path の厳密な一致。使われ方：元の指定 path の照合。 -/
lemma fiberwisePullbackFiberPath_ι :
    fiberwisePullbackFiberPath p f g b ≫ (ihom (Δ[1] : SSet.{u})).map (vertexFiberι p b) =
      vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b ≫
        fiberwiseIntervalPullbackPath p f g ≫
          pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) := by
  rw [fiberwisePullbackFiberPath, Category.assoc, fiberwiseFunctorFiberIso_hom_ι,
    ← Category.assoc, vertexFiberMap_ι, Category.assoc]

/-- 概要：fiber の第一座標の包含は元の第一射影。
方針：fiber 射の包含式。規約：厳密な一致。使われ方：第一入力の保持。 -/
lemma fiberwisePullbackFiberLeft_ι :
    fiberwisePullbackFiberLeft p f g b ≫ vertexFiberι (f ≫ p) b =
      vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b ≫
        fiberwiseIntervalPullbackLeft p f g := vertexFiberMap_ι _ _ _ _ _

/-- 概要：fiber の第二座標の包含は元の第二射影。
方針：fiber 射の包含式。規約：厳密な一致。使われ方：第二入力の保持。 -/
lemma fiberwisePullbackFiberRight_ι :
    fiberwisePullbackFiberRight p f g b ≫ vertexFiberι (g ≫ p) b =
      vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b ≫
        fiberwiseIntervalPullbackRight p f g := vertexFiberMap_ι _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
