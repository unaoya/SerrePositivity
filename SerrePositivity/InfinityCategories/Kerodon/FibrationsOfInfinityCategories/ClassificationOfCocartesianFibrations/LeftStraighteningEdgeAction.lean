module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexRestriction

/-!
概要：straightening の底の実際の辺への作用と単体圏の制限の辺を同定する。
方針：二変数交換の逆性と初頂点写像の一単体の公式を使う。
規約：辺の代表と全パラメーターを厳密に保持する。
使われ方：両端の fiber 同型による既存 transport の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：straightening の転置は、降下で構成した共同図式そのもの。
方針：二変数交換の同値の逆を使う。
規約：関手空間の射の厳密な等式。
使われ方：straightening の底の辺への作用を共同降下で計算する。 -/
lemma leftStraighteningInfinityMap_transpose (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _).symm_apply_apply _

/-- 概要：底の実際の辺を全 left fibrations 上の評価関手の間の辺へ送る。
方針：辺を係数の宇宙へ持ち上げ、straightening の転置で写す。
規約：対象ごとの辺の選択をしない。
使われ方：straightening の実際の transport の作用。 -/
def leftStraighteningInfinityMap_edge {B : SSet.{u}} {b₀ b₁ : B _⦋0⦌}
    (e : SSet.Edge b₀ b₁) :
    SSet.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up b₀)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up b₁))) :=
  ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} e.toTruncated)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B))).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily_vertex _ _)

/-- 概要：終点への制限の辺は、元の底の辺への straightening の作用そのもの。
方針：共同降下の転置と初頂点写像の終点制限の公式を使う。
規約：関手空間の一単体の厳密な等式。
使われ方：終点の比較を元の底の辺の比較へ移す。 -/
lemma leftStraighteningInfinityMap_terminalRestriction_edge {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexRestrictionEdge
      (SimplexCategory.δ (0 : Fin 2)) σ).edge =
    (leftStraighteningInfinityMap_edge (SSet.Edge.mk σ rfl rfl)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B).app (Opposite.op ⦋1⦌)
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction (SimplexCategory.δ (0 : Fin 2)) σ)).edge)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSimplexFirstVertexMap_terminalRestriction]
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B)).app
    (Opposite.op ⦋1⦌) (ULift.up σ)
  rw [leftStraighteningInfinityMap_transpose]

/-- 概要：始点への制限の辺は、始点の指定評価における退化辺。
方針：初頂点写像の始点制限の式と共同図式の退化の自然性を使う。
規約：一単体そのものを同定する。
使われ方：始点側の制限の辺を消去し、fiber 比較を揃える。 -/
lemma leftStraighteningInfinityMap_initialRestriction_edge {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexRestrictionEdge
      (SimplexCategory.δ (1 : Fin 2)) σ).edge =
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).σ 0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)))) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B).app (Opposite.op ⦋1⦌)
    (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction (SimplexCategory.δ (1 : Fin 2)) σ)).edge)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSimplexFirstVertexMap_initialRestriction]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.internalHomFlipHomEquiv_evaluate_vertex]
  exact congrArg (fun f ↦ f (ULift.up (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B).naturality
      (SimplexCategory.σ (0 : Fin 1)).op)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
