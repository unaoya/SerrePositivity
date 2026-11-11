module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionHomotopy

/-!
概要：固定された部分の頂点上のホモトピーの辺の可逆性。
方針：固定条件を一次単体で評価し、頂点上の辺を退化辺と比較する。
規約：ホモトピーの標的の quasicategory 性は要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join の標準単体の変形。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：写像の像を固定するホモトピーは、その像の頂点上で可逆な辺を与える。
方針：固定条件を恒等の辺で評価し、得られる辺が退化していることを使う。
規約：単射性と quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の可逆な変形の頂点での検査。 -/
lemma simplicialHomotopyVertexEdge_isInvertible_of_fixed_map {A B : SSet.{u}}
    {f g : B ⟶ B} (H : SSet.Homotopy f g) (i : A ⟶ B)
    (hi : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ i) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) a)).toTruncated := by
  let v := i.app (Opposite.op ⦋0⦌) a
  have he := congrArg (fun h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B ↦
    h.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hi
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1) at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map] at he
  have he' : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H v).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B) v).edge := by
    change H.h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj B) v).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he').mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (SSet.Truncated.Edge.id (X := (truncation 2).obj B) v))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：fat join の両因子を固定するホモトピーは全頂点で可逆な辺を与える。
方針：各頂点を左または右の因子の像として表す。
規約：因子と fat join の quasicategory 性は不要。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の変形。 -/
lemma fatJoinHomotopy_isInvertible_of_fixed_factors {A B : SSet.{u}}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B} (H : SSet.Homotopy f g)
    (hA : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B)
    (hB : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst B Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B) :
    ∀ x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  intro x
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_vertex_cases A B x
  · exact simplicialHomotopyVertexEdge_isInvertible_of_fixed_map H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B) hA a
  · exact simplicialHomotopyVertexEdge_isInvertible_of_fixed_map H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B) hB b

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
