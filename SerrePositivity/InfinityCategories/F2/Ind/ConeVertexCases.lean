module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeLastFaceRecovery

/-!
概要：元の右余錐の頂点は、元の下方頂点か同じ新しい極大点のいずれか。
方針：零単体の切断位置を二通りに分ける。
規約：元の全包含と指定極大点を保持する。
使われ方：余錐図式の全頂点評価の共終性をまとめる。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：余錐の任意の頂点は元の下方頂点の像か同じ極大点。
方針：切断を列挙。規約：同じ全包含。使われ方：各点評価の共終性。 -/
lemma coneVertex_cases {L : SSet.{u}} (k : (join L (Δ[0] : SSet.{u})) _⦋0⦌) :
    (∃ l : L _⦋0⦌, (joinInl L (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) l = k) ∨
      k = coneApex L := by
  rcases k with ⟨j, x, y⟩
  fin_cases j
  · right
    apply (coneVertex_eq_apex_iff _).mpr
    rfl
  · left
    refine ⟨x, ?_⟩
    cases y
    rfl
end SerrePositivity.InfinityCategories.F2.Ind
