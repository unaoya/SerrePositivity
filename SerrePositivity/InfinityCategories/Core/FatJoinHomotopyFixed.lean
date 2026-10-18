module

public import SerrePositivity.InfinityCategories.Core.FatJoinVertices
public import SerrePositivity.InfinityCategories.Core.PrecompositionHomotopy

/-!
概要：固定された部分の頂点上のホモトピーの辺の可逆性。
方針：固定条件を一次単体で評価し、頂点上の辺を退化辺と比較する。
規約：ホモトピーの標的の quasicategory 性は要求しない。
使われ方：Kerodon §4.6.2 の fat join の標準単体の変形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像の像を固定するホモトピーは、その像の頂点上で可逆な辺を与える。
方針：固定条件を恒等の辺で評価し、得られる辺が退化していることを使う。
規約：単射性と quasicategory 性は不要。
使われ方：Kerodon §4.6.2 の可逆な変形の頂点での検査。 -/
lemma simplicialHomotopyVertexEdge_isInvertible_of_fixed_map {A B : SSet.{u}}
    {f g : B ⟶ B} (H : SSet.Homotopy f g) (i : A ⟶ B)
    (hi : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ i) (a : A _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) a)).toTruncated := by
  let v := i.app (Opposite.op ⦋0⦌) a
  have he := congrArg (fun h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B ↦
    h.app (Opposite.op ⦋1⦌) (PinchedHom.constant a 1, homotopyIntervalEdge.edge)) hi
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (PinchedHom.constant a 1), homotopyIntervalEdge.edge) =
      i.app (Opposite.op ⦋1⦌) (PinchedHom.constant a 1) at he
  rw [pinchedConstant_map] at he
  have he' : (simplicialHomotopyVertexEdge H v).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B) v).edge := by
    change H.h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj B) v).edge,
        homotopyIntervalEdge.edge) = _
    rw [← pinchedConstant_one]
    exact he
  apply (isInvertibleEdge_congr he').mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (SSet.Truncated.Edge.id (X := (truncation 2).obj B) v))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：fat join の両因子を固定するホモトピーは全頂点で可逆な辺を与える。
方針：各頂点を左または右の因子の像として表す。
規約：因子と fat join の quasicategory 性は不要。
使われ方：Kerodon Theorem 4.6.2.8 の標準単体の変形。 -/
lemma fatJoinHomotopy_isInvertible_of_fixed_factors {A B : SSet.{u}}
    {f g : fatJoin A B ⟶ fatJoin A B} (H : SSet.Homotopy f g)
    (hA : (fatJoinInl A B ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ fatJoinInl A B)
    (hB : (fatJoinInr A B ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst B Δ[1] ≫ fatJoinInr A B) :
    ∀ x : (fatJoin A B) _⦋0⦌,
      IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
  intro x
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := fatJoin_vertex_cases A B x
  · exact simplicialHomotopyVertexEdge_isInvertible_of_fixed_map H (fatJoinInl A B) hA a
  · exact simplicialHomotopyVertexEdge_isInvertible_of_fixed_map H (fatJoinInr A B) hB b

end SerrePositivity.InfinityCategories
