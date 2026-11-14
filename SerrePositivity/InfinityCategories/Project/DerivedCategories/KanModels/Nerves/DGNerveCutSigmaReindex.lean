module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutInsertionReindex
/-!
概要：切断集合とその選択点・未選択点の二重添字を削除・挿入の実添字へまとめる。
方針：同じ集合と点を保つ逆写像を構成し、有限和を移す。
規約：実 cochain に使う証明引数を保持する。使われ方：tensor 微分の全和の相殺。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped BigOperators
/-- 選択集合とその点の二重添字を元の削除添字へまとめる。 -/
def dgNerveCutDeletionSigmaEquiv {α : Type u} [DecidableEq α] (T : Finset α) :
    (Σ S : T.powerset, S.val) ≃ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutDeletionIndex T where
  toFun p := ⟨(p.1.val, p.2.val), Finset.mem_powerset.mp p.1.property, p.2.property⟩
  invFun p := ⟨⟨p.val.1, Finset.mem_powerset.mpr p.property.1⟩, ⟨p.val.2, p.property.2⟩⟩
  left_inv p := by cases p; rfl
  right_inv p := by apply Subtype.ext; rfl
/-- 未選択集合と追加点の二重添字を元の挿入添字へまとめる。 -/
def dgNerveCutInsertionSigmaEquiv {α : Type u} [DecidableEq α] (T : Finset α) :
    (Σ S : T.powerset, {j : α // j ∈ T ∧ j ∉ S.val}) ≃ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex T where
  toFun p := ⟨(p.1.val, p.2.val), Finset.mem_powerset.mp p.1.property, p.2.property⟩
  invFun p := ⟨⟨p.val.1, Finset.mem_powerset.mpr p.property.1⟩, ⟨p.val.2, p.property.2⟩⟩
  left_inv p := by cases p; rfl
  right_inv p := by apply Subtype.ext; rfl
/-- 削除の二重和と同じ全添字上の和の比較。 -/
lemma dgNerveCutDeletionSigma_sum {α : Type u} [Fintype α] [DecidableEq α]
    (T : Finset α) {M : Type v} [AddCommMonoid M] (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutDeletionIndex T → M) :
    (∑ S : T.powerset, ∑ j : S.val,
      f ⟨(S.val, j.val), Finset.mem_powerset.mp S.property, j.property⟩) = ∑ p, f p := by
  simpa only [Fintype.sum_sigma, dgNerveCutDeletionSigmaEquiv, Equiv.coe_fn_mk]
    using Equiv.sum_comp (dgNerveCutDeletionSigmaEquiv T) f
/-- 挿入の二重和と同じ全添字上の和の比較。 -/
lemma dgNerveCutInsertionSigma_sum {α : Type u} [Fintype α] [DecidableEq α]
    (T : Finset α) {M : Type v} [AddCommMonoid M] (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex T → M) :
    (∑ S : T.powerset, ∑ j : {j : α // j ∈ T ∧ j ∉ S.val},
      f ⟨(S.val, j.val), Finset.mem_powerset.mp S.property, j.property⟩) = ∑ p, f p := by
  simpa only [Fintype.sum_sigma, dgNerveCutInsertionSigmaEquiv, Equiv.coe_fn_mk]
    using Equiv.sum_comp (dgNerveCutInsertionSigmaEquiv T) f
end SerrePositivity.InfinityCategories.Project.DerivedCategories
