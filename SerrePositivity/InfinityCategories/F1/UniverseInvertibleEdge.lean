module

public import SerrePositivity.InfinityCategories.F1.UniverseInnerFibration
public import SerrePositivity.InfinityCategories.F1.UniverseHomotopy
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation

/-!
概要：可逆辺とその逆の三角形の宇宙持ち上げ。
方針：二次までの単体と面の等式を ULift で写し、同じ両側逆の関係を得る。
規約：元の可逆辺の逆の存在には元の quasicategory 性だけを使う。
使われ方：Kerodon Corollary 5.6.0.6、全空間比較の同値の宇宙持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二次までの辺を宇宙持ち上げする。
方針：一単体と両端点を ULift に入れ、面の等式を写す。
規約：単体集合の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、可逆辺の逆データの移送。 -/
def uliftTruncatedEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X))
      (ULift.up x) (ULift.up y) where
  edge := ULift.up e.edge
  src_eq := congrArg ULift.up e.src_eq
  tgt_eq := congrArg ULift.up e.tgt_eq

/-- 概要：辺の合成三角形を宇宙持ち上げする。
方針：二単体と三つの面の等式を ULift で写す。
規約：三辺の端点は元の端点の持ち上げ。
使われ方：Kerodon Corollary 5.6.0.6、可逆辺の両側の逆関係。 -/
def uliftTruncatedCompStruct {X : SSet.{u}} {x y z : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj X) x z}
    (t : SSet.Truncated.Edge.CompStruct e f g) :
    SSet.Truncated.Edge.CompStruct (uliftTruncatedEdge.{u, v} e)
      (uliftTruncatedEdge f) (uliftTruncatedEdge g) where
  simplex := ULift.up t.simplex
  d₂ := congrArg ULift.up t.d₂
  d₀ := congrArg ULift.up t.d₀
  d₁ := congrArg ULift.up t.d₁

/-- 概要：恒等辺の持ち上げは持ち上げた頂点の恒等辺。
方針：退化の作用と ULift の定義を計算する。
規約：二次までの辺の等式。
使われ方：Kerodon Corollary 5.6.0.6、両側の逆三角形の終端。 -/
lemma uliftTruncatedEdge_id {X : SSet.{u}} (x : X _⦋0⦌) :
    uliftTruncatedEdge.{u, v} (SSet.Truncated.Edge.id x) =
      SSet.Truncated.Edge.id
        (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) (ULift.up x) := rfl

/-- 概要：quasicategory の可逆辺の宇宙持ち上げも可逆。
方針：同じ逆辺と両側の逆三角形を持ち上げ、ホモトピー圏で逆射を構成する。
規約：元の可逆性はホモトピー圏での同型として指定する。
使われ方：Kerodon Corollary 5.6.0.6、可逆なホモトピーの宇宙持ち上げ。 -/
lemma IsInvertibleEdge.ulift {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (he : IsInvertibleEdge e) :
    IsInvertibleEdge (X := (SSet.uliftFunctor.{v, u}).obj X)
      (uliftTruncatedEdge.{u, v} e) := by
  obtain ⟨g, t₁, t₂⟩ := he.nonempty_inverse
  refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk (uliftTruncatedEdge g), ?_, ?_⟩⟩
  · simpa only [uliftTruncatedEdge_id, SSet.Truncated.HomotopyCategory.homMk_id] using
      SSet.Truncated.HomotopyCategory.homMk_comp_homMk (uliftTruncatedCompStruct.{u, v} t₁)
  · simpa only [uliftTruncatedEdge_id, SSet.Truncated.HomotopyCategory.homMk_id] using
      SSet.Truncated.HomotopyCategory.homMk_comp_homMk (uliftTruncatedCompStruct.{u, v} t₂)

/-- 概要：持ち上げたホモトピーの頂点での辺は元の頂点での辺の持ち上げ。
方針：ホモトピーの区間成分と頂点の定値単体を計算する。
規約：辺は二次までの辺として比較する。
使われ方：Kerodon Corollary 5.6.0.6、ホモトピーの点ごとの可逆性の移送。 -/
lemma uliftSimplicialHomotopy_vertexEdge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (simplicialHomotopyVertexEdge (uliftSimplicialHomotopy.{u, v} H) (ULift.up x)).toTruncated =
      uliftTruncatedEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
  apply SSet.Truncated.Edge.ext
  rfl

end SerrePositivity.InfinityCategories
