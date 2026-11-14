module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCutSigns
/-!
概要：選択点の削除と未選択点の挿入の添字を同じ有限和で比較する。
方針：削除と挿入を互いに逆な操作として実同値を構成する。
規約：元の実切断集合と cochain を使う。使われ方：全次元 tensor 候補の HA の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped BigOperators
/-- 同じ実切断の符号と有限和の添字の比較。 -/
abbrev DGNerveCutDeletionIndex {α : Type u} [DecidableEq α] (T : Finset α) :=
  {p : Finset α × α // p.1 ⊆ T ∧ p.2 ∈ p.1}
/-- 同じ実切断の符号と有限和の添字の比較。 -/
abbrev DGNerveCutInsertionIndex {α : Type u} [DecidableEq α] (T : Finset α) :=
  {p : Finset α × α // p.1 ⊆ T ∧ p.2 ∈ T ∧ p.2 ∉ p.1}
/-- 同じ実切断の符号と有限和の添字の比較。 -/
def dgNerveCutInsertionEquiv {α : Type u} [DecidableEq α] (T : Finset α) :
    DGNerveCutDeletionIndex T ≃ DGNerveCutInsertionIndex T where
  toFun p := ⟨(p.val.1.erase p.val.2, p.val.2),
    ⟨fun _ hx => p.property.1 (Finset.mem_erase.mp hx).2,
      p.property.1 p.property.2, Finset.notMem_erase _ _⟩⟩
  invFun p := ⟨(insert p.val.2 p.val.1, p.val.2),
    ⟨Finset.insert_subset p.property.2.1 p.property.1, Finset.mem_insert_self _ _⟩⟩
  left_inv p := by
    apply Subtype.ext
    change (insert p.val.2 (p.val.1.erase p.val.2), p.val.2) = p.val
    rw [Finset.insert_erase p.property.2]
  right_inv p := by
    apply Subtype.ext
    change ((insert p.val.2 p.val.1).erase p.val.2, p.val.2) = p.val
    rw [Finset.erase_insert p.property.2.2]
/-- 同じ実切断の符号と有限和の添字の比較。 -/
lemma dgNerveCutInsertion_sum {α : Type u} [Fintype α] [DecidableEq α]
    (T : Finset α) {M : Type v} [AddCommMonoid M] (F : Finset α → α → M) :
    (∑ p : DGNerveCutDeletionIndex T, F (p.val.1.erase p.val.2) p.val.2) =
      ∑ p : DGNerveCutInsertionIndex T, F p.val.1 p.val.2 := by
  exact Equiv.sum_comp (dgNerveCutInsertionEquiv T) (fun p => F p.val.1 p.val.2)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
