module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningSimplexRestriction

/-!
概要：straightening の底の実際の辺への作用と単体圏の制限の辺を同定する。
方針：二変数交換の逆性と初頂点写像の一単体の公式を使う。
規約：辺の代表と全パラメーターを厳密に保持する。
使われ方：両端の fiber 同型による既存 transport の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：straightening の転置は、降下で構成した共同図式そのもの。
方針：二変数交換の同値の逆を使う。
規約：関手空間の射の厳密な等式。
使われ方：straightening の底の辺への作用を共同降下で計算する。 -/
lemma leftStraighteningInfinityMap_transpose (B : SSet.{u}) :
    transposeFunctorFamily (leftStraighteningInfinityMap B) =
      leftStraighteningSectionJointDiagram B :=
  (internalHomFlipHomEquiv _ _ _).symm_apply_apply _

/-- 概要：底の実際の辺を全 left fibrations 上の評価関手の間の辺へ送る。
方針：辺を係数の宇宙へ持ち上げ、straightening の転置で写す。
規約：対象ごとの辺の選択をしない。
使われ方：straightening の実際の transport の作用。 -/
def leftStraighteningInfinityMap_edge {B : SSet.{u}} {b₀ b₁ : B _⦋0⦌}
    (e : SSet.Edge b₀ b₁) :
    SSet.Edge
      (functorVertex (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (ULift.up b₀)))
      (functorVertex (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (ULift.up b₁))) :=
  ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u, u + 1} e.toTruncated)).map
    (transposeFunctorFamily (leftStraighteningInfinityMap B))).ofEq
    (transposeFunctorFamily_vertex _ _) (transposeFunctorFamily_vertex _ _)

/-- 概要：終点への制限の辺は、元の底の辺への straightening の作用そのもの。
方針：共同降下の転置と初頂点写像の終点制限の公式を使う。
規約：関手空間の一単体の厳密な等式。
使われ方：終点の比較を元の底の辺の比較へ移す。 -/
lemma leftStraighteningInfinityMap_terminalRestriction_edge {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    (leftStraighteningInfinityMap_simplexRestrictionEdge
      (SimplexCategory.δ (0 : Fin 2)) σ).edge =
    (leftStraighteningInfinityMap_edge (SSet.Edge.mk σ rfl rfl)).edge := by
  change (leftStraighteningSectionJointDiagram B).app (Opposite.op ⦋1⦌)
    (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (transportSimplexRestriction (SimplexCategory.δ (0 : Fin 2)) σ)).edge)) = _
  rw [transportSimplexFirstVertexMap_terminalRestriction]
  change _ = (transposeFunctorFamily (leftStraighteningInfinityMap B)).app
    (Opposite.op ⦋1⦌) (ULift.up σ)
  rw [leftStraighteningInfinityMap_transpose]

/-- 概要：始点への制限の辺は、始点の指定評価における退化辺。
方針：初頂点写像の始点制限の式と共同図式の退化の自然性を使う。
規約：一単体そのものを同定する。
使われ方：始点側の制限の辺を消去し、fiber 比較を揃える。 -/
lemma leftStraighteningInfinityMap_initialRestriction_edge {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    (leftStraighteningInfinityMap_simplexRestrictionEdge
      (SimplexCategory.δ (1 : Fin 2)) σ).edge =
    ((ihom (LeftFibrationInfinity B)).obj SpaceInfinity.{u}).σ 0
      (functorVertex (leftStraighteningInfinityMap B ≫ evaluateFunctorAt
        (ULift.up (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)))) := by
  change (leftStraighteningSectionJointDiagram B).app (Opposite.op ⦋1⦌)
    (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (transportSimplexRestriction (SimplexCategory.δ (1 : Fin 2)) σ)).edge)) = _
  rw [transportSimplexFirstVertexMap_initialRestriction]
  rw [leftStraighteningInfinityMap, internalHomFlipHomEquiv_evaluate_vertex]
  exact congrArg (fun f ↦ f (ULift.up (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)))
    ((leftStraighteningSectionJointDiagram B).naturality
      (SimplexCategory.σ (0 : Fin 1)).op)

end SerrePositivity.InfinityCategories
