module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-!
概要：初頂点写像と共同切断評価が反転する辺を同じ集合で指定する。
方針：始点を保つ添字の射の辺を集め、底の退化辺と対象ごとの同値で検証する。
規約：局所化の普遍性は仮定しない。
使われ方：共同切断評価を元の底へ降ろす局所化の比較への入力。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：初頂点を保つ全ての添字の射の辺の集合。
方針：普通の射の nerve の辺として表示して条件を記録する。
規約：退化を含む添字の射も許す。
使われ方：初頂点写像の局所化で反転する辺。 -/
def transportSimplexInitialEdges (B : SSet.{u}) :
    Set ((nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) _⦋1⦌) :=
  {s | ∃ (i j : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) (f : i ⟶ j),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexPreservesFirst f ∧ (nerve.edgeMk f).edge = s}

/-- 概要：係数の宇宙へ揃えた添字の nerve で反転する辺の集合。
方針：元の辺の集合を次数ごとの持ち上げの像で移す。
規約：辺の条件自体は変更しない。
使われ方：空間値の共同評価と初頂点写像を同じ宇宙で比較する。 -/
def transportSimplexInitialEdgesLifted (B : SSet.{u}) :
    Set (((SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B))) _⦋1⦌) :=
  ULift.up '' transportSimplexInitialEdges B

/-- 概要：初頂点写像は指定した全ての辺を反転する。
方針：始点を保つ射の像が実際の退化辺となることを使う。
規約：底の充填性は不要。
使われ方：初頂点写像に沿う局所化の比較を定義する。 -/
lemma transportSimplexFirstVertexMap_inverts (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) (transportSimplexInitialEdges B) := by
  intro s hs
  obtain ⟨i, j, f, hf, rfl⟩ := hs
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (nerve.edgeMk f).edge).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B))).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge from
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_edge_of_preservesFirst f hf)).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：宇宙を揃えた初頂点写像も同じ持ち上げた辺を反転する。
方針：実際の退化辺への等式を次数ごとの持ち上げで写す。
規約：底の quasicategory 性を追加しない。
使われ方：共同切断評価を値の関手空間と同じ宇宙で降ろす。 -/
lemma transportSimplexFirstVertexMap_ulift_inverts (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B))
      (transportSimplexInitialEdgesLifted B) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨i, j, f, hf, rfl⟩ := ht
  have h := congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_edge_of_preservesFirst f hf)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ULift.up (nerve.edgeMk f).edge)).map
      ((truncation 2).map ((SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B)))).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((SSet.uliftFunctor.{u + 1, u}).obj B))
        (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)))).edge from h)).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：全単体の共同切断評価は同じ持ち上げた辺を全対象上で反転する。
方針：始点を保つ制限の大域的可逆性を実際の辺へ適用する。
規約：反転する射を初頂点写像の場合と別に選ばない。
使われ方：局所化の普遍性へ渡す共同評価の反転条件。 -/
lemma transportSimplexSectionInfinity_inverts (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B) (transportSimplexInitialEdgesLifted B) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨i, j, f, hf, rfl⟩ := ht
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ULift.up (nerve.edgeMk f).edge)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B))).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge f).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B)).edge from rfl)).mpr
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_isInvertible_of_preservesFirst f hf)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
